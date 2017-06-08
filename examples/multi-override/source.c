int identity(int x) { return x; }
int example(void) { return identity(1) + identity(2); }
int bad_example(void) { return identity(3); }
