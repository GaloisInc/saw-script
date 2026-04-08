#include <stdlib.h>

extern unsigned __cutpoint__diamonds_true(unsigned *, unsigned *, unsigned *);
extern unsigned __cutpoint__diamonds_false(unsigned *, unsigned *, unsigned *);

unsigned diamonds(unsigned x, unsigned y, unsigned z) {
   if (x) {
      __cutpoint__diamonds_true(&x, &y, &z);
      y += 3;
   }
   else {
      __cutpoint__diamonds_false(&x, &y, &z);
      y -= 3;
   }

   z += y;

   if (x) {
      z += 7;
   }
   else {
      z += 19;
   }
   return z;
}

