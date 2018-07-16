class STAT {
    static int y = 0;

    static int g_imp (int x) { return 0; }
    
    static int f_imp (int x) { return g_imp(x) + 1; }

    static int f_ref (int x) { return 1; }
}
	
