/* Imperative, iterative average computation, in the style of an
   imperative hash.

   The imperative hash implementations in e.g. OpenSSL have this
   style: initialize the state, update the state by hashing
   incrementally one or more times, extract (digest) the hash value at
   the end (e.g. by padding as necessary before hashing a final block
   internally).

   Here we verify a trivial example -- averaging a sequence of numbers
   -- implemnted in the same init, update, digest style.
*/

#include <stdint.h>
#include <stdio.h>

typedef struct {
  uint32_t sum;
  uint32_t len;
} state;

void init(state *st) {
  st->sum = 0;
  st->len = 0;
}

void update(state *st, uint32_t *xs, uint32_t len) {
  for (int i = 0; i < len; ++i ) {
    st->sum += xs[i];
  }
  st->len += len;
}

void digest(state *st, uint32_t *avg) {
  *avg = st->sum / st->len;
}

int main(int argc, char *argv[]) {
  state st;
  init(&st);
  uint32_t xs[] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 };
  uint32_t ys[] = { 10, 11, 12, 13, 14, 15, 16, 17, 18, 19 };
  update(&st, xs, sizeof(xs)/sizeof(uint32_t));
  update(&st, ys, sizeof(ys)/sizeof(uint32_t));
  uint32_t avg;
  digest(&st, &avg);
  printf("The average is %i.\n", avg);
}
