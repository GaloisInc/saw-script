/**
 * pure C hash table for call path throttling.
 *
 * constraints:
 *   - static pool of memory
 *   - uint64_t key
 *   - uint32_t value
 *
 * notes:
 *   - error when pool exhausted : no eviction or reuse policy
 *   - fixed number of buckets: we don't rebalance if some buckets get long
 *     entry chains
 *
 * sottile2@llnl.gov // June 2023
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* global assumptions

   POOLSIZE never changes
   NUMBUCKETS never changes1
*/

typedef struct Entry {
  uint64_t key;
  uint32_t value;
  uint32_t next;
} Entry;

#define POOLSIZE   5
#define NUMBUCKETS 2
#define NULLINDEX UINT32_MAX
#define CAP 5

/* statically allocated pool of slots */
Entry entry_pool[POOLSIZE];

typedef struct PooledHashTable {
  uint32_t buckets[NUMBUCKETS];
  uint32_t cur_entry;
} PooledHashTable;

PooledHashTable ptable;

void init_table() {
  ptable.cur_entry = 0;
  for (int i = 0; i < NUMBUCKETS; i++) {
    ptable.buckets[i] = NULLINDEX;
  }
}

/*
 * djb2 hash function
 */
uint32_t hash(uint64_t v) {
  uint32_t h = 5381;
  uint8_t c;
  for (int i = 0; i < 64; i+=8) {
    c = (v >> i) & 0xff;
    h = 33 * h + c;
  }
  return h;
}

uint32_t get_bucket(uint64_t key) {
  return hash(key) % NUMBUCKETS;
}

uint32_t increment_value(uint64_t key) {
  uint32_t bucket = get_bucket(key);
  uint32_t cur_index = ptable.buckets[bucket];
  uint32_t prev_index = NULLINDEX;

  while (cur_index != NULLINDEX) {
    Entry *cur_entry = &entry_pool[cur_index];
    // key has a slot: increment and return value
    if (cur_entry->key == key) {
      if (cur_entry->value < CAP) {
        cur_entry->value++;
      }
      return cur_entry->value;
    } else {
      prev_index = cur_index;
      cur_index = cur_entry->next;
    }
  }

  if (ptable.cur_entry < POOLSIZE) {
    cur_index = ptable.cur_entry;
    Entry *cur_entry = &entry_pool[cur_index];
    if(prev_index != NULLINDEX)
    {
      Entry *prev_entry =  &entry_pool[prev_index];
      prev_entry->next = ptable.cur_entry;
    }
    else
    {
      ptable.buckets[bucket] = cur_index;
    }
    ptable.cur_entry++;
    cur_entry->key = key;
    cur_entry->next = NULLINDEX;
    cur_entry->value = 1;
    
    return 1;
  }

  return 0;
}

int main(int argc, char **argv) {
  init_table();
  for (int i = 0; i < 2000; i++) {
    uint64_t v = random() % 104;
    uint32_t c = increment_value(v);
    if (c == 0) {
      printf("Could not track %ld: at capacity (%d iterations).\n", v, i);
      break;
    }
    printf("V=%ld C=%d", v, c);
    if (c == CAP) {
      printf(" [CAPPED]");
    }
    printf("\n");
  }
  return 0;
}
