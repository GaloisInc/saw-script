#include<stdint.h>

// Ported from intTests/test_goal_num_ite/test.c. f composes g (double)
// and h (triple) so that f(x) = 6*x. Verified compositionally through
// the g and h overrides; the interesting artifact is how f's several
// proof obligations are ROUTED per-goal to different solvers.

void g(uint64_t* a) {
  *a = 2*(*a);
};

void h(uint64_t* a) {
  *a = 3*(*a);
};

void f(uint64_t* x) {
  g(x);
  h(x);
};
