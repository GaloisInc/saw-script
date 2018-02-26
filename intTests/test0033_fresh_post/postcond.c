void f(unsigned int *x) {
    *x = *x + 1;
};

void g(unsigned int *x) {
    f(x);
}
