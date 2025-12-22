### Test with Test(filepath)
### Runtime: ~7 minutes.

### ----- Init -----
gap> InitF4Graded(6, 2, 4, false);;

### Test that all elements w_a for a in F4 are indeed reflections. Takes 4 minutes.
gap> TestAllReflections();
true

### Test that the Weyl elements have the desired parities.
## In the comments above each expression, we sketch the argument why the corresponding
## expression equals 0.
## We will write d_i for dd(1[ii],1[ii]).
## We will use the following identities from [DMW25, Sections 9 and 10]:
## (1) tr(a)*1_C = a+a'
## (2) tr(ab') = tr(a)tr(b) - tr(ab)
## (3) dd(a[ij],1[ji]) = dd(1[ij],a[ji])
## (4) dd(1[ij], 1[ji]) = g_i g_j (d_i + f_j)
## (Follows from dd(a[ij],a'[ji]) = g_i g_j n(a) (d_i + d_j))
## (5) dd(a[ij], b'[ji]) + dd(b[ij], a'[ji]) = g_i g_j tr(ab') (dd(1[ii],1[ii])+dd(1[jj],1[jj]))
## (6) d_1 + d_2 + d_3 = 2*zeta - xi
## (7) \sum g_i dd(a_i[jl], a_l'a_j'[jl]) = g_1 g_2 g_3 tr(a1a2a3) (2*zeta - xi)
## where the sum runs over all cyclic permutation (i,j,l) of (1,2,3).
gap> test := TestSimpleRootParLists();;

# By (1) and (3), we have
# dd_{1[23],((tr(a1)/g2)*a2')[23]} = 1/g2 dd_{a2[23], tr(a1)[32]} = 1/g2 dd_{a2[23], (a1+a1')[32]}.
# Using also (5) and (2), we infer that the sum of summands 2,3,4 is
# dd_{1[23],((tr(a1)/g2)*a2')[23]}+(1/g2)*dd_{((1)*a1)[23],((1)*a2)[23]}+(1/-g2)*dd_{((1)*a2)[23],((1)*a1')[23]}
# = 1/g2 (dd_{a2[23],a1'[32]} + dd_{a1[23],a2'[32]}) = g3 tr(a1a2') (d_2 + d_3)
# = g3 (tr(a1)tr(a2) - tr(a1a2)) (d_2 + d_3)
# Thus by (6), the sum of the first 4 summands (i.e., all dd-summands) is
# g3 (tr(a1)tr(a2) - tr(a1a2)) (2*zeta - xi).
# Hence the whole sum is 0.
gap> test[1];
dd_{(1)[11],(g3*tr(a1)*tr(a2)-g3*tr(a1a2))[11]}+dd_{((1)*<identity ...>)[23],((tr(a1)/g2)*a2')[23]}+(1/g2)*dd_{((1)*a1)[23],((1)*a2)[23]}+(1/-g2)*dd_{((1)*a2)[23],((1)*a1')[23]}+(g3*tr(a1)*tr(a2)-g3*tr(a1a2))*xi+(-2*g3*tr(a1)*tr(a2)+2*g3*tr(a1a2))*zeta

# By (1),
# dd_{1[23],tr(a1)*a2[23]} = dd_{tr(a1)*1[23],a2[23]} = dd_{a1[23],a2[23]} + dd_{a1'[23],a2[23]} 
gap> test[2];
dd_{((1)*<identity ...>)[23],((-tr(a1)/g3)*a2)[23]}+(1/g3)*dd_{((1)*a1)[23],((1)*a2)[23]}+(1/g3)*dd_{((1)*a1')[23],((1)*a2)[23]}

# The dd-summands are precisely
# 1/(g2g3) * \sum g_i dd_{b_i[jl], b_l'b_j'[jl]}
# where b1 = 1, b2 = a2, b3 = a1, so the whole sum is 0 by (7).
gap> test[3];
dd_{((1)*<identity ...>)[23],((g1/(g2*g3))*(a1'*a2'))[23]}+(1/g2)*dd_{((1)*a1)[12],((1)*a2')[12]}+(1/g3)*dd_{((1)*a2)[31],((1)*a1')[31]}+(g1*tr(a1a2))*xi+(-2*g1*tr(a1a2))*zeta

# Like test[3]: The dd-summands are precisely
# 1/(g1g2) * \sum g_i dd_{b_i[jl], b_l'b_j'[jl]}
# where b1 = 1, b2 = a1', b3 = a2', so the whole sum is 0 by (7).
gap> test[4];
dd_{((1)*<identity ...>)[23],((1/-g2)*(a2*a1))[23]}+(-g3/(g1*g2))*dd_{((1)*a2')[12],((1)*a1)[12]}+(-1/g1)*dd_{((1)*a1')[31],((1)*a2)[31]}+(-g3*tr(a1a2))*xi+(2*g3*tr(a1a2))*zeta

# Like test[3]: The dd-summands are precisely
# 1/(g1g3) * \sum g_i dd_{b_i[jl], b_l'b_j'[jl]}
# where b1 = , b2 = a1, b3 = a2, so the whole sum is 0 by (7).
gap> test[5];
dd_{((1)*<identity ...>)[23],((1/g3)*(a2'*a1'))[23]}+(g2/(g1*g3))*dd_{((1)*a1)[31],((1)*a2')[31]}+(1/g1)*dd_{((1)*a2)[12],((1)*a1')[12]}+(g2*tr(a1a2))*xi+(-2*g2*tr(a1a2))*zeta

# Like test[3]: The dd-summands are precisely
# 1/(g2g3) * \sum g_i dd_{b_i[jl], b_l'b_j'[jl]}
# where b1 = 1, b2 = a2', b3 = a1', so the whole sum is 0 by (7).
gap> test[6];
dd_{((1)*<identity ...>)[23],((g1/(g2*g3))*(a1*a2))[23]}+(1/g3)*dd_{((1)*a2')[31],((1)*a1)[31]}+(1/g2)*dd_{((1)*a1')[12],((1)*a2)[12]}+(g1*tr(a1a2))*xi+(-2*g1*tr(a1a2))*zeta

# Follows from (1) and (2).
gap> test[7];
((-g1*tr(a1)*tr(a2)+g1*tr(a1a2))/g2)*<identity ...>+(g1*tr(a2)/g2)*a1+(-g1/g2)*(a1*a2)+(g1/g2)*(a2*a1')

# -tr(a1a2) = -tr(a2a1) = -a2a1 - a1'a2' and
# tr(a2)a1' = a1'a2 + a1'a2'
gap> test[8];
(-g2*tr(a1a2)/g1)*<identity ...>+(g2*tr(a2)/g1)*a1'+(g2/g1)*(a2*a1)+(-g2/g1)*(a1'*a2)

# Like test[3]: The dd-summands are precisely
# 1/(g1g2) * \sum g_i dd_{b_i[jl], b_l'b_j'[jl]}
# where b1 = a2', b2 = a1', b3 = 1, so the whole sum is 0 by (7).
gap> test[9];
dd_{((1)*<identity ...>)[12],((g3/(g1*g2))*(a1*a2))[12]}+(1/g2)*dd_{((1)*a2')[23],((1)*a1)[23]}+(1/g1)*dd_{((1)*a1')[31],((1)*a2)[31]}+(g3*tr(a1a2))*xi+(-2*g3*tr(a1a2))*zeta

# Like test[3]: The dd-summands are precisely
# 1/(g2g3) * \sum g_i dd_{b_i[jl], b_l'b_j'[jl]}
# where b1 = a1, b2 = a2, b3 = 1, so the whole sum is 0 by (7).
gap> test[10];
dd_{((1)*<identity ...>)[12],((1/g2)*(a2'*a1'))[12]}+(g1/(g2*g3))*dd_{((1)*a1)[23],((1)*a2')[23]}+(1/g3)*dd_{((1)*a2)[31],((1)*a1')[31]}+(g1*tr(a1a2))*xi+(-2*g1*tr(a1a2))*zeta

# Like test[3]: The dd-summands are precisely
# -1/(g1g3) * \sum g_i dd_{b_i[jl], b_l'b_j'[jl]}
# where b1 = a1', b2 = a2', b3 = 1, so the whole sum is 0 by (7).
gap> test[11];
dd_{((1)*<identity ...>)[12],((-1/g1)*(a2*a1))[12]}+(-g2/(g1*g3))*dd_{((1)*a2')[31],((1)*a1)[31]}+(1/-g3)*dd_{((1)*a1')[23],((1)*a2)[23]}+(-g2*tr(a1a2))*xi+(2*g2*tr(a1a2))*zeta

# Like test[3]: The dd-summands are precisely
# 1/(g1g3) * \sum g_i dd_{b_i[jl], b_l'b_j'[jl]}
# where b1 = a2, b2 = a1, b3 = 1, so the whole sum is 0 by (7).
gap> test[12];
dd_{((1)*<identity ...>)[12],((g3/(g1*g2))*(a1'*a2'))[12]}+(1/g1)*dd_{((1)*a1)[31],((1)*a2')[31]}+(1/g2)*dd_{((1)*a2)[23],((1)*a1')[23]}+(g3*tr(a1a2))*xi+(-2*g3*tr(a1a2))*zeta

# By (1), the sum of the last two summands is
# (-1/g1)*dd_{((1)*a2)[12],((1)*a1)[12]}+(-1/g1)*dd_{((1)*a2)[12],((1)*a1')[12]}
# = -1/g1 tr(a1) d_{a2[12],1[12]}
# where, by (3),
# d_{a2[12],1[12]} = d_{a2[12],1[21]} = d_{1[12],a2[21]} = d_{1[12],a2'[12]}.
# Hence by (1), the sum of dd_{1[12],((-tr(a1)/g1)*a2)[12]} with the last two summands is
# -1/g1 tr(a1)tr(a2) d(1[12], 1[12])
# where, by (4),
# d(1[12], 1[12]) = g1g2(d_1 + d_2).
# It follows that the whole sum is zero.
gap> test[13];
dd_{(1)[11],(g2*tr(a1)*tr(a2))[11]}+dd_{((1)*<identity ...>)[12],((-tr(a1)/g1)*a2)[12]}+dd_{(1)[22],(g2*tr(a1)*tr(a2))[22]}+(-1/g1)*dd_{((1)*a2)[12],((1)*a1)[12]}+(-1/g1)*dd_{((1)*a2)[12],((1)*a1')[12]}

# Follows from (1)
gap> test[14];
dd_{((1)*<identity ...>)[12],((-tr(a1)/g2)*a2)[12]}+(1/g2)*dd_{((1)*a1)[12],((1)*a2)[12]}+(1/g2)*dd_{((1)*a1')[12],((1)*a2)[12]}

# Test that we are done
gap> Length(test);
14
