## Elements of ConicAlg and ConicAlgMag
# TODO: Make indeterminates constants that the user cannot change.
a1 := ConicAlgIndet(1);
a2 := ConicAlgIndet(2);
aMag1 := ConicAlgMagIndet(1);
aMag2 := ConicAlgMagIndet(2);
if ConicAlg_rank > 2 then
    a3 := ConicAlgIndet(3);
    aMag3 := ConicAlgMagIndet(3);
fi;
if ConicAlg_rank > 3 then
    a4 := ConicAlgIndet(4);
    aMag4 := ConicAlgMagIndet(4);
fi;
if ConicAlg_rank > 4 then
    a5 := ConicAlgIndet(5);
    aMag5 := ConicAlgMagIndet(5);
fi;
if ConicAlg_rank > 5 then
    a6 := ConicAlgIndet(6);
    aMag6 := ConicAlgMagIndet(6);
fi;

## Elements of Comring
t1 := ComRingIndet(1);
t2 := ComRingIndet(2);
t3 := ComRingIndet(3);
t4 := ComRingIndet(4);
t5 := ComRingIndet(5);
t6 := ComRingIndet(6);
g1 := ComRingGamIndet(1);
g2 := ComRingGamIndet(2);
g3 := ComRingGamIndet(3);

## Elements of Cubic
cubicGen1 := CubicGenericEl(0);
# cubicGen2 := CubicGenericEl(1);
c1 := CubicComEl(1, t1);
c2 := CubicConicEl(2, a1);
c3 := CubicElFromTuple(t1, t2, t3, a1, a2, a1);

## dd as a shorthand for Liedd. TODO: Make this a constant.
dd := Liedd;

## Simple roots
d1 := F4SimpleRoots[1];
d2 := F4SimpleRoots[2];
d3 := F4SimpleRoots[3];
d4 := F4SimpleRoots[4];

## Weyl elements
w1 := GrpStandardWeylF4(F4SimpleRoots[1]);
w1Inv := GrpStandardWeylF4(F4SimpleRoots[1], -1);
w2 := GrpStandardWeylF4(F4SimpleRoots[2]);
w2Inv := GrpStandardWeylF4(F4SimpleRoots[2], -1);
w3 := GrpStandardWeylF4(F4SimpleRoots[3]);
w3Inv := GrpStandardWeylF4(F4SimpleRoots[3], -1);
w4 := GrpStandardWeylF4(F4SimpleRoots[4]);
w4Inv := GrpStandardWeylF4(F4SimpleRoots[4], -1);

# w := GrpWeylF4([1,-1,1,1], g2^-1*g3, -g2*g3^-1)*GrpWeylF4([1,1,-1,1], g3^-1*g1, -g3*g1^-1)
#         *GrpWeylF4([1,1,1,-1], g1^-1*g2, -g1*g2^-1);
# wInv := GrpWeylF4([1,1,1,-1], -g1^-1*g2, g1*g2^-1)*GrpWeylF4([1,1,-1,1], -g3^-1*g1, g3*g1^-1)
#         *GrpWeylF4([1,-1,1,1], -g2^-1*g3, g2*g3^-1);
# func := function(root)
#     local a, l;
#     if root in F4ShortRoots then
#         a := a1;
#     else
#         a := t1;
#     fi;
#     l := LieRootHomF4(root, a);
#     Print(l, "\n");
#     Print(Simplify(w(l)), "\n");
# end;

# funcG2 := function(G2root)
#     local root;
#     for root in F4Roots do
#         if F4RootG2Coord(root) = G2root then
#             Print(root, ":\n");
#             func(root);
#         fi;
#     od;
# end;
# w := GrpStandardWeylF4([1,-1,1,1])*GrpStandardWeylF4([1,1,-1,1])*GrpStandardWeylF4([1,1,1,-1]);
# wInv := GrpStandardWeylF4([1,1,1,-1], -1)*GrpStandardWeylF4([1,1,-1,1], -1)
#         *GrpStandardWeylF4([1,-1,1,1], -1);

# triple := function(a, b, c)
#     local p;
#     Display("J:");
#     p := function(a,b,c)
#         Print(a, ", ", CubicCross(b, c), "\n");
#     end;
#     p(a,b,c);
#     p(b,c,a);
#     p(c,a,b);
#     p := function(a, b, c)
#         Print(CubicCross(a, b), ", ", c, "\n");
#     end;
#     Display("J':");
#     p(a,b,c);
#     p(b,c,a);
#     p(c,a,b);
# end;

# cubId := function(a)
#     local d, d2;
#     d := Simplify(Liedd(a, CubicAdj(a)));
#     d2 := CubicNorm(a) * (2*LieZeta - LieXi);
#     Print(d, " = ", d2, "\n");
# end;

# cubIdLin := function(a, b)
#     local d, d2;
#     d := Liedd(a, CubicAdj(b)) + Liedd(b, CubicCross(a, b));
#     d2 := CubicBiTr(a, CubicAdj(b)) * (2*LieZeta - LieXi);
#     Print(d, " = ", d2, "\n");
# end;

root := [1, 0, 0, -1];
# w := GrpWeylF4(root, a1, a2, true);
# wInv := GrpWeylF4(root, -a1, -a2, true);

# Parity signs for definition of [0,0]-exponentials
checkParity := function(root, weylIndex)
    local delta, w;
    delta := F4SimpleRoots[weylIndex];
    w := GrpStandardWeylF4(delta, -1);
    Display(LieRootHomF4(F4Refl(root, delta), One(ConicAlg)));
    Display(Simplify(w(LieRootHomF4(root, One(ConicAlg)))));
end;
