int flag;
int * const flag_ptr = &flag;
int * flag_ptr2 = &flag;

void foo() { if (flag_ptr2 != flag_ptr) flag_ptr2 = flag_ptr; }
