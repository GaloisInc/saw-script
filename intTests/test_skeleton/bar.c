extern int myglobal;
int bar_sum;

static int baz(int a, int b) { return (a/2) - (b>>2); }

int bar(int arg) {
    if (arg > 8) return arg / 2;
    // bar_sum += 1 + myglobal;  // skeleton doesn't handle globals yet
    return baz(arg, 1);
}
