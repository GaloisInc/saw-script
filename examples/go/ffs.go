package ffs

func ffs_ref(word uint32) uint32 {
	var zero uint32 = 0
	if word == zero {
		return 0
	}
	var cnt uint32
	var n32 uint32 = 32
	var one uint32 = 1
	for cnt = 0; cnt < n32; cnt++ {
		if ((one << cnt) & word) != zero {
			return cnt + one
		}
	}
	return 0
}

func ffs_imp(i uint32) uint32 {
	var n uint32 = 1
	var zero uint32 = 0
	var cffff uint32 = 0xffff
	var c00ff uint32 = 0x00ff
	var c000f uint32 = 0x000f
	var c0003 uint32 = 0x0003
	var n16 uint32 = 16
	var n8 uint32 = 8
	var n4 uint32 = 4
	var n2 uint32 = 2
	var n1 uint32 = 1

	if (i & cffff) == zero {
		n = n + n16
		i = i >> n16
	}
	if (i & c00ff) == zero {
		n = n + n8
		i = i >> n8
	}
	if (i & c000f) == zero {
		n = n + n4
		i = i >> n4
	}
	if (i & c0003) == zero {
		n = n + n2
		i = i >> n2
	}
	if i != zero {
		return (n + ((i + n1) & n1))
	} else {
		return 0
	}
}
