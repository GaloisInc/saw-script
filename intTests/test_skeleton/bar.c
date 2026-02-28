static int baz(int a, int b) { return a - b; }

int bar(int arg) {
    if (arg > 8) return arg / 2;
    return baz(arg, 1);
}
