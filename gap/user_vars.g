# Indeterminates of ConicAlg
if ConicAlg_rank > 0 then
    BindGlobal("a1", ConicAlgIndet(1));
fi;
if ConicAlg_rank > 1 then
    BindGlobal("a2", ConicAlgIndet(2));
fi;
if ConicAlg_rank > 2 then
    BindGlobal("a3", ConicAlgIndet(3));
fi;
if ConicAlg_rank > 3 then
    BindGlobal("a4", ConicAlgIndet(4));
fi;
if ConicAlg_rank > 4 then
    BindGlobal("a5", ConicAlgIndet(5));
fi;
if ConicAlg_rank > 5 then
    BindGlobal("a6", ConicAlgIndet(6));
fi;
# Indeterminates of ComRing
if ComRing_rank > 0 then
    BindGlobal("t1", ComRingIndet(1));
fi;
if ComRing_rank > 0 then
    BindGlobal("t2", ComRingIndet(2));
fi;
if ComRing_rank > 0 then
    BindGlobal("t3", ComRingIndet(3));
fi;
if ComRing_rank > 0 then
    BindGlobal("t4", ComRingIndet(4));
fi;
if ComRing_rank > 0 then
    BindGlobal("t5", ComRingIndet(5));
fi;
if ComRing_rank > 0 then
    BindGlobal("t6", ComRingIndet(6));
fi;
if ComRing_rank > 0 then
    BindGlobal("t7", ComRingIndet(7));
fi;
if ComRing_rank > 0 then
    BindGlobal("t8", ComRingIndet(8));
fi;
if ComRing_rank > 0 then
    BindGlobal("t9", ComRingIndet(9));
fi;
if ComRing_rank > 0 then
    BindGlobal("t10", ComRingIndet(10));
fi;

BindGlobal("g1", ComRingGamIndet(1));
BindGlobal("g2", ComRingGamIndet(2));
BindGlobal("g3", ComRingGamIndet(3));

# dd as a shorthand for Liedd
BindGlobal("dd", Liedd);

# Simple roots
# BindGlobal("d1", F4SimpleRoots[1]);
# BindGlobal("d2", F4SimpleRoots[2]);
# BindGlobal("d3", F4SimpleRoots[3]);
# BindGlobal("d4", F4SimpleRoots[4]);

# Weyl elements
# BindGlobal("w1", GrpStandardWeylF4(F4SimpleRoots[1]));
# BindGlobal("w1Inv", GrpStandardWeylF4(F4SimpleRoots[1], -1));
# BindGlobal("w2", GrpStandardWeylF4(F4SimpleRoots[2]));
# BindGlobal("w2Inv", GrpStandardWeylF4(F4SimpleRoots[2], -1));
# BindGlobal("w3", GrpStandardWeylF4(F4SimpleRoots[3]));
# BindGlobal("w3Inv", GrpStandardWeylF4(F4SimpleRoots[3], -1));
# BindGlobal("w4", GrpStandardWeylF4(F4SimpleRoots[4]));
# BindGlobal("w4Inv", GrpStandardWeylF4(F4SimpleRoots[4], -1));
