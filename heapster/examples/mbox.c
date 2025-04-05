
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/////////////////////////////////////////////////////////////////////////////////////
// Types of errors charbydis may make

#define SUCCESS 0
#define INVALID_LENGTH 1
#define NO_POLICY_FOR_THIS_CONNECTION 2
#define NO_STATE_FOR_THIS_CONNECTION 3
#define SAD_OUT_OF_MEMORY 4
#define TRANSPORT_MODE_UNSUPPORTED 5
#define INVALID_SEQUENCE_NUMBER 6
#define UNKNOWN_SPI 7
#define MBOX_ALREADY_FREED 8
#define MBOX_OUT_OF_MEMORY 9
#define INVALID_PROTOCOL 10
#define BUFFER_COPY_ERROR 11
#define MBOX_COPY_ERROR 12
#define MBOX_SPLIT_ERROR 13
#define PARSE_ERROR 14
#define FILE_ERROR 15
#define SAD_STATE_SRC_MISSING 16
#define SAD_STATE_DST_MISSING 17
#define SAD_STATE_SPI_MISSING 18
#define SAD_STATE_MODE_MISSING 19
#define SAD_STATE_AUTH_ALGO_MISSING 20
#define SAD_STATE_ENC_ALGO_MISSING 21
#define UNIMPLEMENTED 22
#define MBOX_NULL_ERROR 23
#define SAD_KEY_MISSING 24
#define AUTH_FAILURE 25

typedef uint32_t error;

char *err_str(error e) {
    switch (e) {
        case SUCCESS:
            return "success";
        case INVALID_LENGTH:
            return "invalid length";
        case NO_POLICY_FOR_THIS_CONNECTION:
            return "no policy for this connection";
        case NO_STATE_FOR_THIS_CONNECTION:
            return "no state for this connection";
        case SAD_OUT_OF_MEMORY:
            return "SAD is out of memory";
        case TRANSPORT_MODE_UNSUPPORTED:
            return "transport mode is unsupported";
        case INVALID_SEQUENCE_NUMBER:
            return "invalid sequence number";
        case UNKNOWN_SPI:
            return "unknown SPI";
        case MBOX_ALREADY_FREED:
            return "mbox already freed";
        case MBOX_OUT_OF_MEMORY:
            return "mbox out of memory";
        case INVALID_PROTOCOL:
            return "packet contains invalid protocol";
        case BUFFER_COPY_ERROR:
            return "error copying buffers";
        case MBOX_COPY_ERROR:
            return "error copying mboxes";
        case MBOX_SPLIT_ERROR:
            return "error splitting mboxes";
        case PARSE_ERROR:
            return "parse error";
        case SAD_STATE_SRC_MISSING:
            return "SAD src field missing";
        case SAD_STATE_DST_MISSING:
            return "SAD dst field missing";
        case SAD_STATE_SPI_MISSING:
            return "SAD spi field missing";
        case SAD_STATE_MODE_MISSING:
            return "SAD esp_mode field missing";
        case SAD_STATE_AUTH_ALGO_MISSING:
            return "SAD auth_algo field missing";
        case SAD_STATE_ENC_ALGO_MISSING:
            return "SAD enc_algo field missing";
        case UNIMPLEMENTED:
            return "unimplemented";
        case MBOX_NULL_ERROR:
            return "tried to operate on a null mbox pointer";
        case SAD_KEY_MISSING:
            return "SAD key is missing";
        case AUTH_FAILURE:
            return "authentication failed";
    }
    return "unknown error";
}

/////////////////////////////////////////////////////////////////////////////////////
// memory management

#define MBOX_SIZE 128

typedef struct mbox {
    size_t start;
    size_t len;
    struct mbox *next;
    uint8_t data[MBOX_SIZE];
} mbox;

#include <stdlib.h>
#include <string.h>
#include <strings.h>

#define MEM_POOL_SIZE 10000
#define MIN(x, y) (((x) < (y)) ? (x) : (y))

static mbox mem_pool[MEM_POOL_SIZE];
static bool mem_in_use[MEM_POOL_SIZE] = {false};
static size_t search_index = 0;  // Avoid searching through the whole pool

#include <stdio.h>

bool mbox_all_freed() {
    for (size_t i = 0; i < MEM_POOL_SIZE; i++) {
        if (mem_in_use[i]) {
            printf("mbox %lu in use\n", i);
            return false;
        }
    }
    return true;
}

mbox *mbox_new() {
    // Linear scan through the mem_pool, looking for an available mbox.
    for (; search_index < MEM_POOL_SIZE; search_index++) {
        if (!mem_in_use[search_index]) {
            // Found one. Initialize it.
            mem_in_use[search_index] = true;
            mbox *m = &mem_pool[search_index];
            // bzero(m, sizeof(mbox));
            memset(m, 0, sizeof(mbox));
            m->len = MBOX_SIZE;
            search_index += 1;
            return m;
        }
    }
    return NULL;
}

error mbox_free(mbox *m) {
    if (m == NULL) {
        return 0;
    }
    size_t mid = m - mem_pool;
    if (mem_in_use[mid]) {
        mem_in_use[mid] = false;
        search_index = MIN(search_index, mid);
        return 0;
    }
    return MBOX_ALREADY_FREED;
}

error mbox_free_chain(mbox *m) {
    while (m != NULL) {
        mbox *mbox_next = m->next;
        error err = mbox_free(m);
        if (err != 0) {
            return err;
        }
        m = mbox_next;
    }
    return 0;
}

mbox *mbox_from_buffer(const uint8_t *inp, size_t len) {
    mbox *head = mbox_new();
    if (head == NULL) {
        return NULL;
    }
    if (len < MBOX_SIZE) {
        // If the size of the data is small, we only need one mbox
        memcpy(head->data, inp, len);
        head->len = len;
        return head;
    } else {
        // Start the mbox chain
        memcpy(head->data, inp, MBOX_SIZE);
    }
    mbox *prev = head;
    for (size_t i = MBOX_SIZE; i < len; i += MBOX_SIZE) {
        // Get a new mbox
        mbox *cur = mbox_new();
        if (cur == NULL) {
            return NULL;
        }
        // Add it to the chain
        prev->next = cur;
        if (len - i < MBOX_SIZE) {
            // If we're at the end of data, end the chain
            memcpy(cur->data, inp + i, len - i);
            cur->len = len - i;
        } else {
            // Otherwise copy away
            memcpy(cur->data, inp + i, MBOX_SIZE);
        }
        prev = cur;
    }
    return head;
}

size_t mbox_to_buffer(uint8_t *buf, size_t buf_len, const mbox *m, size_t offset) {
    if (m == NULL) {
        return 0;
    }
    // Exhaust offset first
    if (m->len < offset) {
        return mbox_to_buffer(buf, buf_len, m->next, offset - m->len);
    }
    // Follow the mbox chain, copying bytes into the output buffer
    size_t bytes_copied = 0;
    while (m != NULL) {
        // printf("buf_len = %lu, bytes_copied = %lu, m->len = %lu, offset =
        // %lu\n",
        //         buf_len, bytes_copied, m->len, offset);
        if (buf_len - bytes_copied < m->len - offset) {
            // Ran out of space in the output buffer
            // Fill up the remaining and abort
            size_t amt_remaining = buf_len - bytes_copied;
            memcpy(buf + bytes_copied, m->data + m->start + offset, amt_remaining);
            return bytes_copied + amt_remaining;
        }
        memcpy(buf + bytes_copied, m->data + m->start + offset, m->len - offset);
        bytes_copied += m->len - offset;
        offset = 0;
        m = m->next;
    }
    return bytes_copied;
}

void mbox_to_buffer_rec(uint8_t *buf, size_t buf_len, const mbox *m) {
    if (m == NULL) {
        return;
    }
    size_t bytes_to_copy = m->len;
    if (buf_len >= bytes_to_copy) {
        // buffer bigger than mbox
        memcpy(buf, m->data + m->start, bytes_to_copy);
        mbox_to_buffer_rec(buf + bytes_to_copy, buf_len - bytes_to_copy, m->next);
    } else {
        // buffer smaller than mbox
        memcpy(buf, m->data + m->start, buf_len);
    }
    return;
}

size_t mbox_len(const mbox *m) {
    // Add up the cumulative lengths of the mbox chain
    size_t total = 0;
    while (m != NULL) {
        total += m->len;
        m = m->next;
    }
    return total;
}

void mbox_concat(mbox *x, mbox *y) {
    if (x != NULL) {
        x->next = y;
    }
}

void mbox_concat_chains(mbox *x, mbox *y) {
    if (x == NULL || y == NULL) {
      return;
    }

    // Find the last item in the chain of x
    while (1) {
        if (x->next == NULL) {
            break;
        }
        x = x->next;
    }
    mbox_concat(x, y);
}

// Drop and de-allocate bytes from the start of an mbox.
void mbox_drop(mbox *m, size_t ix) {
    if (m == NULL) {
        return;
    } else if (ix >= m->len) {
        mbox_drop(m->next, ix - m->len);
        m->start = 0;
        m->len = 0;
        return;
    }
    m->start = m->start + ix;
    m->len = m->len - ix;
}

// Extract the first ix bytes into its own mbox.
// Returns the mbox starting at ix, and modifies m to contain only the rest
mbox *mbox_split_at(mbox **m, size_t ix) {
    if (m == NULL || *m == NULL) {
        return NULL;
    } else if (ix == 0) {
        mbox* ret = *m;
        *m = NULL;
        return ret;
    } else if (ix == (*m)->len) {
        mbox* nxt = (*m)->next;
        (*m)->next = NULL;
        return nxt;
    } else if (ix > (*m)->len) {
        return mbox_split_at(&((*m)->next), ix - (*m)->len);
    }

    mbox *new = mbox_new();
    if (new == NULL) {
        return NULL;
    }

    memcpy(new->data, (*m)->data + ix, (*m)->len - ix);
    new->len = (*m)->len - ix;
    new->next = (*m)->next;
    (*m)->next = NULL;
    (*m)->len = ix;

    return new;
}

// Copy a single mbox
mbox *mbox_copy(const mbox *src) {
    if (src == NULL) {
        return NULL;
    }
    mbox *dst = mbox_new();
    if (dst == NULL) {
        return 0;  // Out of memory
    }
    memcpy(dst->data + src->start, src->data + src->start, src->len);
    dst->start = src->start;
    dst->len = src->len;
    return dst;
}

// Clone a whole mbox chain
mbox *mbox_copy_chain(const mbox *src, size_t len) {
    if (len == 0) {
        return NULL;
    }
    mbox *head = mbox_copy(src);
    if (head == NULL || src == NULL) {
        return NULL;
    }
    if (head->len >= len) {
        head->len = len;
        return head;
    }
    mbox *rest = mbox_copy_chain(src->next, len - head->len);
    if (rest != NULL) {
        mbox_concat(head, rest);
    }
    return head;
}

// Detach the first mbox from the chain, returning it.
mbox *mbox_detach(mbox **m) {
    if (*m == NULL) {
        return NULL;
    }
    mbox *n = *m;
    *m = (*m)->next;
    n->next = NULL;
    return n;
}

mbox *mbox_detach_from_end(mbox **m, size_t length_from_end) {
    return mbox_split_at(m, mbox_len(*m) - length_from_end);
}

// Treat the bytes inside m as an integer, incrementing them
// Useful for IVs
error mbox_increment(mbox *m) {
    if (m == NULL) {
        return MBOX_NULL_ERROR;
    }
    if (MBOX_SIZE != 128 || m->start != 0 || m->len != MBOX_SIZE) {
        return UNIMPLEMENTED;
    }

    // Heapster doesn't like the casts in the following couple lines, so they
    // are reimplemented in a hideous way below.
    if (++((uint64_t *)m->data)[0] == 0) {
        ++((uint64_t *)m->data)[1];
    }

    // Here is how to perform this computation in a little-endian way:
    /*
    for (uint64_t i = 0; i < 16; ++i) {
      if (++(m->data[i]) == 0)
        break;
    }
    */

    // first 64 bits
    // uint64_t byte0 = m->data[0]; uint64_t byte1 = m->data[1];
    // uint64_t byte2 = m->data[2]; uint64_t byte3 = m->data[3];
    // uint64_t byte4 = m->data[4]; uint64_t byte5 = m->data[5];
    // uint64_t byte6 = m->data[6]; uint64_t byte7 = m->data[7];
    // uint64_t joined_bytes =
    //   (byte0 << 56) & (byte1 << 48) & (byte2 << 40) & (byte3 << 32) &
    //   (byte4 << 24) & (byte5 << 16) & (byte6 << 8) & byte7;
    // joined_bytes++;
    // printf("joined bytes: %lu\n", joined_bytes);
    // printf("should be: %lu\n", ++((uint64_t *)m->data)[0]);
    // byte0 = (joined_bytes & 0xFF00000000000000) >> 56;
    // byte1 = (joined_bytes & 0x00FF000000000000) >> 48;
    // byte2 = (joined_bytes & 0x0000FF0000000000) >> 40;
    // byte3 = (joined_bytes & 0x000000FF00000000) >> 32;
    // byte4 = (joined_bytes & 0x00000000FF000000) >> 24;
    // byte5 = (joined_bytes & 0x0000000000FF0000) >> 16;
    // byte6 = (joined_bytes & 0x000000000000FF00) >> 8;
    // byte7 = (joined_bytes & 0x00000000000000FF);
    // m->data[0] = byte0; m->data[1] = byte1;
    // m->data[2] = byte2; m->data[3] = byte3;
    // m->data[4] = byte4; m->data[5] = byte5;
    // m->data[6] = byte6; m->data[7] = byte7;

    // if (joined_bytes == 0) {
    //     byte0 = m->data[8];  byte1 = m->data[9];
    //     byte2 = m->data[10]; byte3 = m->data[11];
    //     byte4 = m->data[12]; byte5 = m->data[13];
    //     byte6 = m->data[14]; byte7 = m->data[15];
    //     joined_bytes =
    //       (byte0 << 56) & (byte1 << 48) & (byte2 << 40) & (byte3 << 32) &
    //       (byte4 << 24) & (byte5 << 16) & (byte6 << 8) & byte7;
    //     joined_bytes++;
    //     byte0 = (joined_bytes & 0xFF00000000000000) >> 56;
    //     byte1 = (joined_bytes & 0x00FF000000000000) >> 48;
    //     byte2 = (joined_bytes & 0x0000FF0000000000) >> 40;
    //     byte3 = (joined_bytes & 0x000000FF00000000) >> 32;
    //     byte4 = (joined_bytes & 0x00000000FF000000) >> 24;
    //     byte5 = (joined_bytes & 0x0000000000FF0000) >> 16;
    //     byte6 = (joined_bytes & 0x000000000000FF00) >> 8;
    //     byte7 = (joined_bytes & 0x00000000000000FF);
    //     m->data[8] = byte0;  m->data[9] = byte1;
    //     m->data[10] = byte2; m->data[11] = byte3;
    //     m->data[12] = byte4; m->data[13] = byte5;
    //     m->data[14] = byte6; m->data[15] = byte7;
    // }
    return SUCCESS;
}

error mbox_randomize(mbox *m) {
    if (m == NULL) {
        return MBOX_NULL_ERROR;
    }
    for (size_t i = m->start; i < m->len; i++) {
        m->data[i] = rand();
    }
    return SUCCESS;
}

// returns 1 if the two mboxes are equal, 0 if they are not
int mbox_eq(mbox *m, mbox *n) {
    if (m == NULL && n == NULL) {
        // If they are both NULL, they are equal
        return 1;
    }
    if (m == NULL || n == NULL) {
        // If only one is NULL, they are unequal
        return 0;
    }

    size_t mi = m->start;  // current index into m
    size_t ni = n->start;  // current index into n
    while (1) {
        if (m == NULL && n == NULL) {
            // If they are both NULL, they are equal
            return 1;
        }
        if (m == NULL || n == NULL) {
            // If only one is NULL, they are unequal
            return 0;
        }
        if (m->data[mi++] != n->data[ni++]) {
            return 0;
        }
        if (mi >= m->len) {
            m = m->next;
            if (m != NULL) {
                mi = m->start;
            }
        }
        if (ni >= n->len) {
            n = n->next;
            if (n != NULL) {
                ni = n->start;
            }
        }
    }
    return 1;
}
