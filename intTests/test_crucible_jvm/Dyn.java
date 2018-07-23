class Dyn {
    int x = 0;

    Dyn d;

    int g (int y) {
	return x + y;
    }
    
    static int f_imp (int y) {
	Dyn d = new Dyn();
	return d.x + y;
    }

    static int f_virt (int y) {
	Dyn d = new Dyn();
	return d.g(y);
    }

    
    static int f_ref (int y) { return y; }

    Dyn() {
	this.x = 0;
	this.d = null;
    }

    
    Dyn(int y) {
	this.x = y;
	this.d = new Dyn();
    }

    static int h_imp (int y) {
	Dyn d1 = new Dyn (y);
	return d1.d.g(4);
    }

    static int h_ref (int y) {
	return y+4;
    }
   
    
}
