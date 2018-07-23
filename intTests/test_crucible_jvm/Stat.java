class Stat {
    static int y = 1+1;

    static int g_imp (int x) { return y; }
    
    static int f_imp (int x) { return g_imp(x) + 1; }

    static int f_ref (int x) { return 4; }

    public Stat () {} 
}
	
