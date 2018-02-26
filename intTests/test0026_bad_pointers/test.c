#include <stdlib.h>
#include <stdio.h>

int read_after_free()
{  
  volatile int* x = malloc(sizeof(int));
  *x = 1;
  free((int*) x);
  return *x; // <- error here, read after free
}

int write_after_free()
{  
  volatile int* x = malloc(sizeof(int));
  *x = 42;
  free((int*) x);
  *x = 12;  // <- error here, write after free
  return 1;
}

int double_free()
{  
  volatile int* x = malloc(sizeof(int));
  *x = 12;
  free((int*) x);
  free((int*) x); // <- error here, double free
  return 1;
}

int test_equal( void* x, void* y ) {
  return (x == y);
}

int test_lt( void* x, void* y ) {
  return (x < y);
}

int equals_after_free()
{
  volatile int* x = malloc(sizeof(int));
  *x = 12;
  free((int*) x);
  if( test_equal( (void*) x, (void*) x) ) { puts("EQ!"); }
  return 1;
}

int le_after_free()
{
  volatile char* x = malloc(32);
  volatile char* y = x + 5;
  free((void*) x);
  if( test_lt( (void*) x, (void*) y ) ) { puts("LT!"); }
  return 1;
}

int le_different_allocs()
{
  volatile int* x = malloc(sizeof(int));
  volatile int* y = malloc(sizeof(int));
  *x = 12;
  *y = 32;
  if( test_lt( (void*) x, (void*) y ) ) { puts("LT!"); }
  return 1;
}

// Intentionally leak the address of a local variable
int* leak_pointer()
{
  volatile int x;
  volatile int* y = &x;
  *y = 1;
  return (int*) y; // <- leak a pointer to local variable
}

int read_after_stack_free()
{
  int * x = leak_pointer();
  return *x; // <- error here, read an invald local variable pointer
}

int write_after_stack_free()
{
  int * x = leak_pointer();
  *x = 12; // <- error here, write an invalid local varible pointer
  return 1;
}

int free_after_stack_free()
{
  int * x = leak_pointer();
  free(x); // <- error here, free an invalid local variable pointer
  return 1;
}

// Wrap `free` in a function, so clang doesn't notice
// and optimize away the bogus local free below.
void subfn(void* x) {
  free(x);
}

int free_local()
{
  volatile int x = 12;
  subfn((int*) &x);  // <- error here, free a local variable
  return 1;
}

int equals_after_stack_free()
{
  int * x = leak_pointer();
  int * y = malloc(sizeof(int));
  if( test_equal( x, y ) ) { puts("EQ!"); }
  return 1;
}

int lt_after_stack_free()
{
  int * x = leak_pointer();
  int * y = leak_pointer();
  if( test_lt( x, y ) ) { puts("LT!"); }
  return 1;
}

char global_string[] = "asdf\n";
int free_global()
{
  char* x = global_string;
  free(x); // <- error here, free a global variable
  return 1;
}
