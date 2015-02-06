(benchmark sawscript
   :logic QF_AUFBV
   :extrafuns ((t0 BitVec[32]))
   :extrapreds ((c0)
                (c1))
   :assumption (iff c0 c1)
   :formula c0)