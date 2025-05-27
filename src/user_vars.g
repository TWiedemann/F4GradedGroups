## Elements of ConicAlg
a1 := ConicAlgBasicIndet(1);
a2 := ConicAlgBasicIndet(2);
# a3 := ConicAlgBasicIndet(3);
# a4 := ConicAlgBasicIndet(4);
# a5 := ConicAlgBasicIndet(5);
# a6 := ConicAlgBasicIndet(6);

## Elements of ConicAlgMag
aMag1 := ConicAlgMagBasicIndet(1);
aMag2 := ConicAlgMagBasicIndet(2);
# aMag3 := ConicAlgMagBasicIndet(3);
# aMag4 := ConicAlgMagBasicIndet(4);
# aMag5 := ConicAlgMagBasicIndet(5);
# aMag6 := ConicAlgMagBasicIndet(6);

## Elements of Comring
t1 := ComRingBasicIndet(1);
t2 := ComRingBasicIndet(2);
t3 := ComRingBasicIndet(3);
t4 := ComRingBasicIndet(4);
t5 := ComRingBasicIndet(5);
t6 := ComRingBasicIndet(6);
g1 := ComRingGamIndet(1);
g2 := ComRingGamIndet(2);
g3 := ComRingGamIndet(3);

## Elements of Cubic
cubicGen1 := CubicGenericEl(0);
# cubicGen2 := CubicGenericEl(1);
c1 := CubicComEl(1, t1);
c2 := CubicAlgEl(2, a1);
c3 := CubicElFromTuple(t1, t2, t3, a1, a2, a1);

## Simple roots
d1 := F4SimpleRoots[1];
d2 := F4SimpleRoots[2];
d3 := F4SimpleRoots[3];
d4 := F4SimpleRoots[4];

## Weyl elements
w1 := GrpStandardWeylF4(F4SimpleRoots[1]);
w1Inv := GrpStandardWeylInvF4(F4SimpleRoots[1]);
w2 := GrpStandardWeylF4(F4SimpleRoots[2]);
w2Inv := GrpStandardWeylInvF4(F4SimpleRoots[2]);
w3 := GrpStandardWeylF4(F4SimpleRoots[3]);
w3Inv := GrpStandardWeylInvF4(F4SimpleRoots[3]);
w4 := GrpStandardWeylF4(F4SimpleRoots[4]);
w4Inv := GrpStandardWeylInvF4(F4SimpleRoots[4]);