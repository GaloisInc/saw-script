int flag;
int * const flag_ptr = 0; // same as foo.c except this initialization
int * flag_ptr2 = 0;

void foo() { if (flag_ptr2 != flag_ptr) flag_ptr2 = flag_ptr; }
