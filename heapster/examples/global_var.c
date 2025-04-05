#include <stdlib.h>
#include <stdint.h>

/* A very simple acquire/release lock for some shared data */

int64_t shared_data = 0;
int64_t lock = 0;

/* A spin lock; returns 1 after acquireing lock, otherwise runs forever.
   (Not robust to concurrent semantics) */
int64_t acquire_lock(int64_t** data) {
  while (lock != 0) {
    continue;
 }
  lock = 1;
  *data = &shared_data;
  return 1;
}

/* To be called after a thread is done accessing the shared data. */ 
void release_lock(void) {
  lock = 0;
  return;
}


int64_t acquire_release_acquire_release(void) {

  int64_t* data;
  acquire_lock(&data);
  *data = 42;
  release_lock();
  
  acquire_lock(&data);
  if (data == NULL) {
    return -1;
  }
  int64_t val = *data;
  release_lock();
  return val;
}

int64_t acquire_release_fail(void) {
  int64_t* data;
  acquire_lock(&data);
  *data = 42;
  release_lock();

  *data = 84;

  // shared data should still be 42
  acquire_lock(&data);
  int64_t val = *data;
  release_lock();
  return val;
}
