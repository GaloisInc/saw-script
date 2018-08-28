class Dyn implements Iface {
    int x;
    Dyn d;

    public int g (int y) {
	return this.x + y;
    }

    public int binary (int y, boolean b) {
	if (b) { return y + x; }
	else { return x;      }
    }

    static int b (int y) {
	Dyn d = new Dyn();
	return d.binary(y, true);
    }
    
    // instance variable access
    static int f_imp (int y) {
	Dyn d = new Dyn();
	return d.x + y;
    }

    static int f_virt (int y) {
	Dyn d = new Dyn();
	return d.g(y);
    }

    
    static int f_ref (int y) { return y + 2; }


    Dyn() {
	this.x = 2;
	this.d = null;
    }

    
    Dyn(int y, Dyn b0) {
	this.x = y;
	this.d = new Dyn();
    }

    static int h_imp (int y) {
	Dyn d1 = new Dyn ();
	d1.d = new Dyn(y,null);
	return d1.d.g(4);
    }

    static int h_ref (int y) {
	return y+4;
    }


    static int i_imp (int y) {
	Iface d = new Dyn ();

	return d.g(y);

    }
   
    
}
