// voidTest.c

/** mockup of subroutine to assume/override */
void clear_void(void *arr, unsigned int size) {
    unsigned char *cArr = arr;
    for (int i = 0; i < size; i++) {
        cArr[i] = 0;
    }
}

/** mockup of caller that passes a pointer to an array of unsigned ints to the void *-based subroutine */
void clear_uints(unsigned int *uints, unsigned int numUInts) {
    clear_void(uints, numUInts * sizeof(unsigned int));
}