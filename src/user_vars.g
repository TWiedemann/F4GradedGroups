## Elements of ConicAlg and ConicAlgMag
a1 := ConicAlgBasicIndet(1);
a2 := ConicAlgBasicIndet(2);
aMag1 := ConicAlgMagBasicIndet(1);
aMag2 := ConicAlgMagBasicIndet(2);
if ConicAlg_rank > 2 then
    a3 := ConicAlgBasicIndet(3);
    aMag3 := ConicAlgMagBasicIndet(3);
fi;
if ConicAlg_rank > 3 then
    a4 := ConicAlgBasicIndet(4);
    aMag4 := ConicAlgMagBasicIndet(4);
fi;
if ConicAlg_rank > 4 then
    a5 := ConicAlgBasicIndet(5);
    aMag5 := ConicAlgMagBasicIndet(5);
fi;
if ConicAlg_rank > 5 then
    a6 := ConicAlgBasicIndet(6);
    aMag6 := ConicAlgMagBasicIndet(6);
fi;

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

w := GrpWeylF4([1,-1,1,1], g2^-1*g3, -g2*g3^-1)*GrpWeylF4([1,1,-1,1], g3^-1*g1, -g3*g1^-1)
        *GrpWeylF4([1,1,1,-1], g1^-1*g2, -g1*g2^-1);
wInv := GrpWeylF4([1,1,1,-1], -g1^-1*g2, g1*g2^-1)*GrpWeylF4([1,1,-1,1], -g3^-1*g1, g3*g1^-1)
        *GrpWeylF4([1,-1,1,1], -g2^-1*g3, g2*g3^-1);
func := function(root)
    local a, l;
    if root in F4ShortRoots then
        a := a1;
    else
        a := t1;
    fi;
    l := LieRootHomF4(root, a);
    Print(l, "\n");
    Print(Simplify(w(l)), "\n");
end;

funcG2 := function(G2root)
    local root;
    for root in F4Roots do
        if F4RootG2Coord(root) = G2root then
            Print(root, ":\n");
            func(root);
        fi;
    od;
end;
# w := GrpStandardWeylF4([1,-1,1,1])*GrpStandardWeylF4([1,1,-1,1])*GrpStandardWeylF4([1,1,1,-1]);
# wInv := GrpStandardWeylInvF4([1,1,1,-1])*GrpStandardWeylInvF4([1,1,-1,1])
#         *GrpStandardWeylInvF4([1,-1,1,1]);

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
w := GrpWeylF4(root, a1, a2, true);
wInv := GrpWeylF4(root, -a1, -a2, true);

checkParity := function(root, weylIndex)
    local delta, w;
    delta := F4SimpleRoots[weylIndex];
    w := GrpStandardWeylInvF4(delta);
    Display(LieRootHomF4(F4Refl(root, delta), One(ConicAlg)));
    Display(Simplify(w(LieRootHomF4(root, One(ConicAlg)))));
end;