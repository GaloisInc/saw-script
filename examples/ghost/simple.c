int next(void) {
        static int i = 0;
        return i++;
}

int example(void) {
        next();
        next();
        return next();
}
