#include <stdlib.h>
#include <stdint.h>

/* A very simple acquire/release lock for some shared data */

int64_t shared_data;
int64_t lock = 0;

/* Returns 1 if able to acquire lock, at which point the user can read from
   and write to the shared data. Returns 0 otherwise.
 */
int64_t acquire_lock(void) {
  if (lock == 1) {
    return 0;
  } else {
    lock = 1;
    return 1;
  }
}

/* To be called after a thread is done accessing the shared data. */ 
void release_lock(void) {
  lock = 0;
  return;
}

/* Should only be called after a lock is acquired to avoid data races. */
void write_data(int64_t data) {
  shared_data = data;
}

/* Should only be called after a lock is acquired to avoid data races. */
int64_t get_data(void) {
  return shared_data;
}

void test(void) {

  // Should fail since we haven't acquired a lock yet
  // write_data(32);

  acquire_lock();
  write_data(84);
  release_lock();

  // should fail since get_data comes after release_lock
  // However: currently does not fail
  // write_data(22);
  return;
}
