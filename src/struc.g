# This file should be obsolete
strucConst := One(ComRing); # eta in Tom, 3.3

strucZero := function()
	local result;
	result := NullMat(2, 2, ComRing);
	result[1][2] := cubicZero();
	result[2][1] := cubicZero();
	return result;
end;

IsStrucEl := function(S)
	if IsList(S) and Length(S)=2 then
		if IsList(S[1]) and Length(S[1])=2 and IsList(S[2]) and Length(S[2])=2 then
			if S[1][1] in ComRing and S[2][2] in ComRing and IsCubicEl(S[1][2]) and IsCubicEl(S[2][1]) then
				return true;
			else
				return false;
			fi;
		else
			return false;
		fi;
	else
		return false;
	fi;
end;

strucEl := function(t1, A1, A2, t2)
	if t1 in ComRing and t2 in ComRing and IsCubicEl(A1) and IsCubicEl(A2) then
		return [ [ t1, A1 ], [ A2, t2 ] ];
	else
		return fail;
	fi;
end;

strucGenericEl := function(i)
	local cubic1, cubic2, com1, com2;
	cubic1 := cubicGenericElForIndets(8*i+1, 8*i+2, 8*i+3, 6*i+1, 6*i+2, 6*i+3);
	cubic2 := cubicGenericElForIndets(8*i+4, 8*i+5, 8*i+6, 6*i+4, 6*i+5, 6*i+6);
	com1 := comRingBasicIndet(8*i+7);
	com2 := comRingBasicIndet(8*i+8);
	return strucEl(com1, cubic1, cubic2, com2);
end;

# Involution of the Brown algebra
strucInv := function(S)
	return strucEl(S[2][2], S[1][2], S[2][1], S[1][1]);
end;

# Not an actual involution, but used in the definition of the grading of the Brown algebra
strucPseudoInv := function(S)
	return strucEl(S[2][2], S[2][1], S[1][2], S[1][1]);
end;

strucMult := function(S, T)
	local M11, M12, M21, M22;
	M11 := S[1][1] * T[1][1] + strucConst * cubicTr(S[1][2], T[2][1]);
	M12 := S[1][1]*T[1][2] + T[2][2]*S[1][2] + strucConst * cubicCross(S[2][1], T[2][1]);
	M21 := S[2][2]*T[2][1] + T[1][1]*S[2][1] + cubicCross(S[1][2], T[1][2]);
	M22 := S[2][2]*T[2][2] + strucConst*cubicTr(S[2][1], T[1][2]);
	return strucEl(M11, M12, M21, M22);
end;

strucV := function(S, T, U)
	return strucMult(strucMult(S, strucInv(T)), U) + strucMult(strucMult(U, strucInv(T)), S) - strucMult(strucMult(U, strucInv(S)), T);
end;

strucVTwist := function(S, T, U)
	return strucV(S, strucPseudoInv(T), U);
end;

strucSkew := function(S, T)
	return strucMult(S, strucInv(T)) - strucMult(T, strucInv(S));
end;

# Upper right
strucConicURHom := function(i, j, a)
	return strucEl(Zero(ComRing), cubicAlgEl(i, j, a), cubicZero(), Zero(ComRing));
end;

# Lower left
strucConicLLHom := function(i, j, a)
	return strucEl(Zero(ComRing), cubicZero(), cubicAlgEl(i, j, a), Zero(ComRing));
end;

# root: A short root in the 1-part of F_4, given in the linear combination format
# a: An element of ConicAlg
# Output: The corresponding element of the Brown algebra
strucConicHom := function(root, a)
	if root = [ 1, 1, 1, 0 ] then
		return strucConicURHom(1, 2, a);
	elif root = [ 1, 1, 1, 1 ] then
		return strucConicURHom(1, 3, a);
	elif root = [ 1, 1, 2, 1 ] then
		return strucConicURHom(2, 3, a);
	elif root = [ 1, 2, 3, 2 ] then
		return strucConicLLHom(1, 2, a);
	elif root = [ 1, 2, 3, 1 ] then
		return strucConicLLHom(1, 3, a);
	elif root = [ 1, 2, 2, 1 ] then
		return strucConicLLHom(2, 3, a);
	else
		return fail;
	fi;
end;

strucConicHomByIndet := function(i)
	return strucConicHom(conicAlgBasicIndet(i));
end;

# Upper right
strucComURHom := function(i, t)
	return strucEl(Zero(ComRing), cubicComEl(i, t), cubicZero(), Zero(ComRing));
end;

# Lower left
strucComLLHom := function(i, t)
	return strucEl(Zero(ComRing), cubicZero(), cubicComEl(i, t), Zero(ComRing));
end;

# Diagonal of Brown algebra
strucComDiagHom := function(i, t)
	local result;
	result := strucZero();
	result[i][i] := t;
	return result;
end;

strucComHom := function(root, t)
	if root = [ 1, 0, 0, 0 ] then
		return strucComDiagHom(2, t);
	elif root = [ 1, 1, 0, 0 ] then
		return strucComURHom(1, t);
	elif root = [ 1, 1, 2, 0 ] then
		return strucComURHom(2, t);
	elif root = [ 1, 2, 2, 0 ] then
		return strucComLLHom(3, t);
	elif root = [ 1, 3, 4, 2 ] then
		return strucComDiagHom(1, t);
	elif root = [ 1, 2, 4, 2 ] then
		return strucComLLHom(1, t);
	elif root = [ 1, 2, 2, 2 ] then
		return strucComLLHom(2, t);
	elif root = [ 1, 1, 2, 2 ] then
		return strucComURHom(3, t);
	else
		return fail;
	fi;
end;

strucComHomByIndet := function(root, i)
	return strucComHom(root, comRingBasicIndet(i));
end;

strucHom := function(root, x)
	if root in F4Grad1ShortLC and x in ConicAlg then
		return strucConicHom(root, x);
	elif root in F4Grad1LongLC and x in ComRing then
		return strucComHom(root, x);
	else
		return fail;
	fi;
end;

strucHomByIndet := function(root, i)
	if F4RootIsShort(root) then
		return strucHom(root, conicAlgBasicIndet(i));
	else
		return strucHom(root, comRingBasicIndet(i));
	fi;
end;

strucGetNonTrivCoeff := function(S)
	local i, coeff;
	# First check the diagonal
	for i in [1, 2] do
		if S[i][i] <> Zero(ComRing) then
			return S[i][i];
		fi;
	od;
	# Then check the upper right
	coeff := cubicGetNonTrivCoeff(S[1][2]);
	if coeff <> Zero(ComRing) then
		return coeff;
	else # Check the lower left
		return cubicGetNonTrivCoeff(S[2][1]);
	fi;
end;

# Returns true if S is element of the root space in the Brown algebra corresponding to root, otherwise false
strucElIsInRootSpace := function(root, S)
	local coeff, T;
	coeff := strucGetNonTrivCoeff(S);
	if coeff in [ Zero(ComRing), Zero(ConicAlg) ] then
		return true;
	else
		T := strucHom(root, coeff);
		return ((S = T) and (T <> fail));
	fi;
end;

## Verifying the grading

strucCheckGrading := function()
	local root1, root2, root3, testEl, rootSum, bOk;
	for root1 in F4Grad1LC do
		for root2 in F4Grad1LC do
			for root3 in F4Grad1LC do
				testEl := strucVTwist(strucHomByIndet(root1, 1), strucHomByIndet(root2, 2), strucHomByIndet(root3, 3));
				rootSum := root1 - root2 + root3;
				if rootSum in F4Grad1LC then
					bOk := strucElIsInRootSpace(rootSum, testEl);
				else
					bOk := (testEl = strucZero());
				fi;
				if not bOk then
					Print("Problem for ", root1, " - ", root2, " + ", root3, "\n");
				fi;
			od;
		od;
	od;
end;

## Auxiliary for finding root spaces

strucFindLong := function()
	local a1, a2, a3;
	a1 := ConicAlg.1;
	a2 := ConicAlg.2;
	a3 := ConicAlg.3;
	Display("1000 = 1110 - 1221 + 1111:");
	Display(strucVTwist(strucConicURHom(1, 2, a1), strucConicLLHom(2, 3, a2), strucConicURHom(1, 3, a3)));
	Display("1220 = 1110 - 1111 + 1221:");
	Display(strucVTwist(strucConicURHom(1, 2, a1), strucConicURHom(1, 3, a3), strucConicLLHom(2, 3, a2)));
	Display("1222 = 1221 - 1110 + 1111:");
	Display(strucVTwist(strucConicLLHom(2, 3, a2), strucConicURHom(1, 2, a1), strucConicURHom(1, 3, a3)));
	Display("1100 = 1221 - 1231 + 1110:");
	Display(strucVTwist(strucConicLLHom(2, 3, a1), strucConicLLHom(1, 3, a2), strucConicURHom(1, 2, a3)));
	Display("1342 = 1221 - 1110 + 1231:");
	Display(strucVTwist(strucConicLLHom(2, 3, a1), strucConicURHom(1, 2, a3), strucConicLLHom(1, 3, a2)));
	Display("1220 = 1221 - 1232 + 1231:");
	Display(strucVTwist(strucConicLLHom(2, 3, a1), strucConicLLHom(1, 2, a2), strucConicLLHom(1, 3, a3)));
	Display("1222 = 1221 - 1231 + 1232:");
	Display(strucVTwist(strucConicLLHom(2, 3, a1), strucConicLLHom(1, 3, a3), strucConicLLHom(1, 2, a2)));
end;

strucCheckSubComUR := function(i)
	local t1, t2, t3;
	t1 := ComRing.1;
	t2 := ComRing.2;
	t3 := ComRing.3;
	Display(strucVTwist(strucComURHom(i, t1), strucComURHom(3-i, t2), strucComURHom(i, t3)));
end;

strucCheckSubComLL := function(i)
	local t1, t2, t3;
	t1 := ComRing.1;
	t2 := ComRing.2;
	t3 := ComRing.3;
	Display(strucVTwist(strucComLLHom(i, t1), strucComLLHom(i, t2), strucComLLHom(i, t3)));
end;

strucCheckSubComDiag := function(i)
	local t1, t2, t3;
	t1 := ComRing.1;
	t2 := ComRing.2;
	t3 := ComRing.3;
	Display(strucVTwist(strucComDiagHom(i, t1), strucComDiagHom(3-i, t2), strucComDiagHom(i, t3)));
end;

strucCheckSubAlgUR := function(i, j)
	local a1, a2, a3;
	a1 := ConicAlg.1;
	a2 := ConicAlg.2;
	a3 := ConicAlg.3;
	Display(strucVTwist(strucConicURHom(i, j, a1), strucConicURHom(i, j, a2), strucConicURHom(i, j, a3)));
end;

strucCheckSubAlgLL := function(i, j)
	local a1, a2, a3;
	a1 := ConicAlg.1;
	a2 := ConicAlg.2;
	a3 := ConicAlg.3;
	Display(strucVTwist(strucConicLLHom(i, j, a1), strucConicLLHom(i, j, a2), strucConicLLHom(i, j, a3)));
end;

test := function(x, y)
	Display(strucMult(x, strucInv(y)));
end;
# x := strucConicURHom(1, 2, a1);
# y := strucConicLLHom(2, 3, a2);
# z := strucConicURHom(1, 3, a3);
x := strucConicLLHom(2, 3, a1);
y := strucConicLLHom(1, 3, a2);
z := strucConicURHom(1, 2, a3);
x2 := strucConicLLHom(2, 3, a1);
y2 := strucConicLLHom(1, 2, a2);
z2 := strucConicLLHom(1, 3, a3);
strucCheckTomConj := function()
	local a1, a2, a3, test;
	a1 := ConicAlg.1;
	a2 := ConicAlg.2;
	a3 := ConicAlg.3;

	test(strucConicURHom(1, 2, a1), strucConicLLHom(2, 3, a2));
	test(strucConicURHom(1, 3, a3), strucConicURHom(1, 2, a1));
	test(strucConicLLHom(2, 3, a1), strucConicLLHom(1, 3, a2));
	test(strucConicLLHom(2, 3, a1), strucConicURHom(1, 2, a3));
	test(strucConicLLHom(2, 3, a1), strucConicLLHom(1, 2, a2));
	test(strucConicLLHom(2, 3, a1), strucConicLLHom(1, 2, a2));
end;

## Experimental

# strucQ := function(S, T)
	# return 1/2 * strucVTwist(S, T, S);
# end;

# strucBerg := function(S, T)
	# return function(U)
		# return U - strucVTwist(S, T, U) + strucQ(S, strucQ(T, U));
	# end;
# end;

# posMap, negMap: Maps from the Brown algebra to itself
# Checks whether (posMap, negMap) is compatible with strucVTwist
# checkStrucHom := function(posMap, negMap)
	# local l, i, j, k, x, y, z, result1, result2, result;
	# l := Length(F4Grad1LC);
	# for i in [1..l] do
		# for j in [1..l] do
			# for k in [1..l] do
				# x := strucHomByIndet(F4Grad1LC[i], 1);
				# y := strucHomByIndet(F4Grad1LC[j], 2);
				# z := strucHomByIndet(F4Grad1LC[k], 3);
				# result1 := strucVTwist(posMap(x), negMap(y), posMap(x));
				# result2 := posMap(strucVTwist(x,y,z));
				# result := result1 - result2;
				# if result <> strucZero() then
					# Display(result);
				# fi;
			# od;
		# od;
	# od;
# end;