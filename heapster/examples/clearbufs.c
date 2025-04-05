#include <stdlib.h>
#include <stdint.h>

typedef struct bufs {
  struct bufs * next;
  int64_t len;
  int64_t data [];
} bufs;

void clearbufs (bufs * lst)
{
  // NOTE: the input value of lst is stored in a stack-allocated variable, which
  // is also called lst below, but is called lp in the paper. This is sort-of
  // like the following code, except that the following would actually make a
  // second stack slot for variable lp, unlike the paper example.
  //
  // bufs **lp = alloca(8)
  // *lp = lst;

  while (1) {
    // NOTE: reading lst here and testing for NULL 
    //
    // bufs *l = lst = *lp
    // if (l == NULL) { ... }
    if (lst == NULL) {
      return;
    } else {
      lst->data[0] = 0;
      lst = lst->next;
    }
  }
}
