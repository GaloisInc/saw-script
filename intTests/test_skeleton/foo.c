int myglobal = 0;

extern int bar(int);

int foo(int arg, char c) {
    myglobal += arg;
    return bar(arg);
}
