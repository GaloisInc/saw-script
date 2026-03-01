int myglobal = 0;

extern int bar(int);

int foo(int arg, char c) {
    // myglobal += arg;   // skeleton doesn't support globals yet
    return bar(arg);
}
