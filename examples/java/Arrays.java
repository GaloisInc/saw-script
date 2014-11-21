class Arrays {
    void unit(int a[]) {
        for(int i = 0; i < a.length; i++) a[i] = 0;
        a[0] = 1;
    }

    void copy(int a[], int b[]) {
        for(int i = 0; i < a.length; i++) b[i] = a[i];
    }

    int sum(int a[]) {
        int sum = 0;
        for(int i = 0; i < a.length; i++) sum += a[i];
        return sum;
    }

    void comp(int a[]) {
        unit(a);
    }
}
