extern int myglobal;
int bar_sum;

static int baz(int a, int b) { return a - b; }

int bar(int arg) {
    if (arg > 8) return arg / 2;
    bar_sum += 1 + myglobal;
    return baz(arg, 1);
}
