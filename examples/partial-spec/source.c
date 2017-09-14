struct my_nested {
        int counter1;
        int counter2;
};

struct my_struct {
    unsigned int counter;
    char *p;
};

void inc(struct my_struct *s) {
        s->counter++;
}

unsigned int use_inc(void) {
        struct my_struct m = { .counter = 0 };
        inc(&m);
        return m.counter;
}
