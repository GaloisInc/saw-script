#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

struct buffer {
    size_t len;
    uint8_t data[];
};

typedef struct buffer buffer;

buffer *buffer_alloc(size_t len)
{
    buffer *buf = malloc(sizeof(struct buffer) + (sizeof(uint8_t) * len));
    if(buf) {
        buf->len = len;
    }
    return buf;
}

buffer *buffer_create(const uint8_t *data, size_t len)
{
    buffer *buf = buffer_alloc(len);
    if(!buf) {
        return 0;
    }

    memcpy(buf->data, data, len);
    return buf;
}

buffer *buffer_copy(const buffer *buf)
{
    return buffer_create(buf->data, buf->len);
}
