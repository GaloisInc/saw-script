#include <stdlib.h>

extern size_t __cutpoint__add3a(size_t *);
extern size_t __cutpoint__add3b(size_t *);

size_t add3(size_t x) {
   x++;
   __cutpoint__add3a(&x);
   x++;
   __cutpoint__add3b(&x);
   x++;
   return x;
}
