class Arr {

    public static int[] one = { 1, 2, 3 };
    public static int[] onea = { 0, 0, 0 };
    
    public static int[][] two = { { 1, 2 } };
	
    public static Dyn[] dyns = { new Dyn() };

    static int main(int x) {
	return single(x) + doub(x) + obj(x) + cp (x);
    }

    static int single(int x) {
	return one[x];
    }

    static int doub(int x) {
	return two[x][x];
    }

    static int obj(int y) {
	return dyns[y].x;
    }

    static int cp (int y) {
	System.arraycopy (one, 0, onea, 0, 3 );
	return onea[y];
    }

	 
}
