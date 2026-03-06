extern int foo(char inparr[], int idx);
extern int bar(int arg);

int baz(int a) {
    return bar(foo("Hello, world!", a));
}

int main(int argc, char **argv) {
    return baz(argc);
}

// n.b. "$ ./main 1 2 3; echo $?" displays 55 (4 args, 4th char is 'o' or 111, /2 = 55
