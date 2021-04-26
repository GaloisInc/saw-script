class Sub extends Dyn {

    public int g (int x) {
	return x + 17;
    }

    public static int dyn(int x) {
        Dyn s = new Sub();
        return s.g(x);
    }

    public static int sub(int x) {
	Sub s = new Sub();
	return s.g(x);
    }

}
