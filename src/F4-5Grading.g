## Obsolete?

K := Rationals; # Ground field

## The root system F_4
F4Vec := FullRowSpace(K, 4); # Euclidean space containing F_4

# Simple roots in F_4: 1-2>3-4
F4Sim := [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]];
# Shortcuts
f := F4Sim;
f1 := f[1];
f2 := f[2];
f3 := f[3];
f4 := f[4];

# Returns a list of all positive roots in F_4 in the linear combination format
F4ComputePosSysLC := function()
	local f1, f2, f3, f4;
	f1 := f[1];
	f2 := f[2];
	f3 := f[3];
	f4 := f[4];
	return [ f1, f2, f3, f4, f1+f2, f2+f3, f3+f4, f1+f2+f3, f2+2*f3, f2+f3+f4, f1+f2+2*f3, f1+f2+f3+f4, f2+2*f3+f4, f1+2*f2+2*f3, f1+f2+2*f3+f4, f2+2*f3+2*f4, f1+2*f2+2*f3+f4, f1+f2+2*f3+2*f4, f1+2*f2+3*f3+f4, f1+2*(f2+f3+f4), f1+2*f2+3*f3+2*f4, f1+2*f2+4*f3+2*f4, f1+3*f2+4*f3+2*f4, 2*f1+3*f2+4*f3+2*f4 ]; # Positive Roots in the order given by Vavilov-Plotkin
end;

F4PosLC := F4ComputePosSysLC();
F4NegLC := -F4PosLC;
F4RootsLC := Concatenation(F4PosLC, F4NegLC);

HeightLC := function(root)
	return(Sum(root));
end;

# ----- Functions for inner product and reflections in F_4 ---

# alpha, beta: Roots in F_4, given as linear combinations of simple roots
# Output: Their inner product
F4InnerProduct := function(alpha, beta)
	local mat;
	# mat[i][j] is the inner product of f[i] with f[j]
	mat := [[ 2, -1, 0, 0], [ -1, 2, -1, 0 ], [ 0, -1, 1, -1/2 ], [ 0, 0, -1/2, 1 ] ];
	return alpha * mat * beta;
end;

F4CartanInt := function(alpha, beta)
	return 2 * F4InnerProduct(alpha, beta) / F4InnerProduct(beta, beta);
end;

# alpha, beta: Roots in F_4 in the linear combination format
# Output: sigma_alpha(beta) in the linear combination format
F4refl := function(alpha, beta)
	return beta - (2 * F4InnerProduct(alpha, beta) / F4InnerProduct(alpha, alpha))*alpha;
end;

# alpha: Root in F_4 in the linear combination format
# Output: Set of all roots in F_4 which are orthogonal to alpha (in the linear combination format)
F4OrthogonalRoots := function(alpha)
	local result, beta;
	result := [];
	for beta in F4PosLC do
		if F4InnerProduct(alpha, beta) = 0 then
			Add(result, beta);
			Add(result, -beta);
		fi;
	od;
	return result;
end;

# root: Root in F_4 in the linear combination format
# Output: true if root is short, otherwise false
F4RootIsShort := function(root)
	if F4InnerProduct(root, root) = 1 then
		return true;
	else
		return false;
	fi;
end;

F4RootsAreAdjacent := function(alpha, beta)
	return not (alpha + beta in F4RootsLC);
end;

# Input: A list of roots in F_4 in the linear combination format
# Output: [ shortList, longList ] where shortList contains all the short roots in rootList and longList all the long ones
F4SplitListByLength := function(rootList)
	local shortList, longList, alpha;
	shortList := [];
	longList := [];
	for alpha in rootList do
		if F4RootIsShort(alpha) then
			Add(shortList, alpha);
		else
			Add(longList, alpha);
		fi;
	od;
	return [ shortList, longList ];
end;

## ----- Grading ---

F4HighestRootLC := 2*f1+3*f2+4*f3+2*f4;

F4ComputeGrad1LC := function()
	local result, alpha, beta;
	result := [];
	for alpha in F4RootsLC do
		for beta in F4RootsLC do
			if alpha + beta = F4HighestRootLC then
				if not alpha in result then
					Add(result, alpha);
				fi;
			fi;
		od;
	od;
	return result;
end;

F4Grad2LC := [ F4HighestRootLC ];
F4Grad1LC := F4ComputeGrad1LC();
F4Grad1ShortLC := F4SplitListByLength(F4Grad1LC)[1];
F4Grad1LongLC := F4SplitListByLength(F4Grad1LC)[2];
F4GradNeg1LC := -F4Grad1LC;
F4GradNeg1ShortLC := -F4Grad1ShortLC;
F4GradNeg1LongLC := -F4Grad1LongLC;
F4GradNeg2LC := -F4Grad2LC;
F4Grad0LC := Difference(F4RootsLC, Concatenation(F4Grad1LC, F4Grad2LC, F4GradNeg1LC, F4GradNeg2LC));

F4CheckIs5GradLC := function(grad1, grad2)
	local gradNeg1, gradNeg2, grad0, grad, alpha, beta, gamma, bFound;
	gradNeg1 := -grad1;
	gradNeg2 := -grad2;
	grad0 := Difference(F4RootsLC, Concatenation(grad1, grad2, gradNeg1, gradNeg2));
	# Axiom 1: If alpha is i-graded, beta is j-graded and alpha+beta is a root, then alpha+beta is (i+j)-graded
	grad := function(root)
		if root in grad1 then
			return 1;
		elif root in grad2 then
			return 2;
		elif root in grad0 then
			return 0;
		elif root in gradNeg1 then
			return -1;
		elif root in gradNeg2 then
			return -2;
		else
			return fail;
		fi;
	end;
	for alpha in F4RootsLC do
		for beta in F4RootsLC do
			if alpha + beta in F4RootsLC then
				if grad(alpha) + grad(beta) <> grad(alpha+beta) then
					Print("Axiom 1 not satisfied for roots ", alpha, ", ", beta, "\n");
					return false;
				fi;
			fi;
		od;
	od;
	# Axiom 2: Every 0-graded root is the difference of two 1-graded roots
	for alpha in grad0 do
		bFound := false;
		for beta in grad1 do
			for gamma in grad1 do
				if beta - gamma = alpha then
					bFound := true;
					break;
				fi;
			od;
			if bFound then
				break;
			fi;
		od;
		if not bFound then
			Print("Axiom 2 not satisfied for root ", alpha, "\n");
			return false;
		fi;
	od;
	# Everything was ok
	return true;
end;

### ----- Folding F_4 -> G_2 -----

## The subspaces W1 and W2 of F4Vec
# List of basis vectors
W1BasList := [ f1, 3*f2 + 4*f3 + 2*f4 ];
W2BasList := [ f3, f4 ];
# The subspaces
W1 := Subspace(F4Vec, W1BasList);
W2 := Subspace(F4Vec, W2BasList);
# The bases as basis objects in GAP
W1Bas := Basis(W1, W1BasList);
W2Bas := Basis(W2, W2BasList);
F4VecWBas := Basis(F4Vec, Concatenation(W1BasList, W2BasList)); # Basis of F4Vec

## Projection maps
# alpha: Element of F4Vec
# Output: The projection on alpha onto W1 or W2, respectively
projW1 := function(alpha)
	local coeff, vectors;
	coeff := Coefficients(F4VecWBas, alpha);
	vectors := Concatenation(W1BasList, [Zero(F4Vec), Zero(F4Vec)]);
	return coeff * vectors;
end;
projW2 := function(alpha)
	local coeff, vectors;
	coeff := Coefficients(F4VecWBas, alpha);
	vectors := Concatenation([Zero(F4Vec), Zero(F4Vec)], W2BasList);
	return coeff * vectors;
end;

G2Roots0 := Set(List(F4RootsLC, projW1));
G2Roots := Filtered(G2Roots0, alpha -> (alpha <> Zero(F4Vec)));
G2Sim := [ projW1(f2), projW1(f1) ];
g1 := G2Sim[1]; # Short simple root
g2 := G2Sim[2]; # Long simple root

# G2Root: An element of G2Roots0
# Output: The preimage of G2Root under projW1 in F4RootsLC
projW1Inv := function(G2Root)
	return Filtered(F4RootsLC, alpha -> (projW1(alpha) = G2Root));
end;

G2RootIsShort := function(G2Root)
	return (F4InnerProduct(G2Root, G2Root) = 2/3);
end;

# i: An integer.
# Output: The corresponding root in G2 if these roots are ordered "clockwise" with g1 being the first root and g2 being the sixth root.
G2RootByClockOrder := function(i)
	if i > 12 then
		return G2RootByClockOrder(RemInt(i, 12));
	fi;
	# See https://en.wikipedia.org/wiki/File:Base_for_the_G2_root_system.png
	if i = 1 then
		return g1;
	elif i = 2 then
		return 3*g1 + g2;
	elif i = 3 then
		return 2*g1 + g2;
	elif i=4 then
		return 3*g1 + 2*g2;
	elif i=5 then
		return g1+g2;
	elif i=6 then
		return g2;
	else
		return -G2RootByClockOrder(i-6);
	fi;
end;

# Output: The unique integer i from 1 to 12 such that G2Root = G2RootByClockOrder(i)
G2RootGetClockOrder := function(G2Root)
	local i;
	for i in [1..12] do
		if G2Root = G2RootByClockOrder(i) then
			return i;
		fi;
	od;
	return fail;
end;

testG2 := function()
	return Set(G2Roots) = Set(List([1..12], G2RootByClockOrder));
end;

# rootSystem: A root system (as a set of roots, not as a root system in GAP).
# rootList: A subset of rootSystem.
# Output: The root subsystem generated by rootList.
generatedSubsystem := function(rootSystem, rootList)
	local vecspace, subspace;
	vecspace := VectorSpace(K, rootSystem);
	subspace := Subspace(vecspace, rootList);
	return Intersection(rootSystem, subspace);
end;

# rootlist: A set of roots in F4RootsLC which forms a root subsystem
# Output: True if this subsystem is of type C_3
subsystemIsC3 := function(rootlist)
	local vecspace;
	vecspace := VectorSpace(K, rootlist);
	if Dimension(vecspace) = 3 and Length(rootlist) = 18 and Number(rootlist, F4RootIsShort) = 12 then
		return true;
	else
		return false;
	fi;
end;

getAllC3Subsystems := function()
	local result, alpha, beta, gamma, subsys;
	result := [];
	# Very inefficient, but fast enough
	for alpha in F4PosLC do
		for beta in F4PosLC do
			for gamma in F4PosLC do
				subsys := Set(generatedSubsystem(F4RootsLC, [ alpha, beta, gamma ]));
				if subsystemIsC3(subsys) and not subsys in result then
					Add(result, subsys);
				fi;
			od;
		od;
	od;
	return result;
end;

testG2ShortPreimage := function()
	local alpha, preim, preimShort, preimLong, i, j, scp, subsys, e;
	for alpha in Filtered(G2Roots, G2RootIsShort) do
		preim := projW1Inv(alpha);
		preimShort := Filtered(preim, F4RootIsShort);
		preimLong := Difference(preim, preimShort);
		if not (Length(preimShort) = 3 and Length(preimLong) = 3) then
			return false;
		fi;
		e := 1/2 * preimLong;
		# Check that e[1], e[2], e[3] are pairwise orthogonal
		for i in [1..3] do
			for j in [1..3] do
				scp := F4InnerProduct(e[i], e[j]);
				if i <> j and scp <> 0 then
					return false;
				fi;
			od;
		od;
		if Set([e[1]+e[2], e[1]+e[3], e[2]+e[3]]) <> Set(preimShort) then
			return false;
		fi;
		subsys := generatedSubsystem(F4RootsLC, preim);
		if not subsystemIsC3(subsys) then
			return false;
		fi;
	od;
	return true;
end;

testG2LongPreimage := function()
	local alpha, preim;
	for alpha in G2Roots do
		if not G2RootIsShort(alpha) then
			preim := projW1Inv(alpha);
			if not (Length(preim) = 1 and not F4RootIsShort(preim[1])) then
				return false;
			fi;
		fi;
	od;
	return true;
end;

testSubspacesOrtho := function()
	local a, b;
	for a in W1BasList do
		for b in W2BasList do
			if F4InnerProduct(a, b) <> 0 then
				return false;
			fi;
		od;
	od;
	return true;
end;

# Returns true if:
# - For all beta in G_2 short with long roots alpha_1, ..., alpha_3 in the preimage,
# we have projW1(gamma^{\sigma(alpha_1 ... alpha_3)}) = projW1(gamma)^{\sigma(beta)}
# for all gamma in F_4.
# - For all beta in G_2 long with long root alpha in the preimage,
# we have projW1(gamma^{\sigma(alpha)}) = projW1(gamma)^{\sigma(beta)}
# for all gamma in F_4.
# If one of these conditions is not satisfied, then returns false.
testFoldWeylAction := function()
	local gamma, beta, preimLong, perm, permList, refl1, refl2;
	for beta in G2Roots do
		preimLong := Filtered(projW1Inv(beta), x -> not F4RootIsShort(x));
		# The assertion should hold for any ordering of the roots in the preimage,
		# so we iterate through all permutations of preimLong
		if G2RootIsShort(beta) then # Size(preimLong) = 3
			permList := [[1,2,3], [1,3,2], [2,1,3], [2,3,1], [3,1,2], [3,2,1]];
		else # Size(preimLong) = 1
			permList := [[1]];
		fi;
		for perm in permList do
			refl1 := function(x)
				local i;
				for i in perm do
					x := F4refl(preimLong[i], x);
				od;
				return x;
			end;
			refl2 := x -> F4refl(beta, x);
			for gamma in F4RootsLC do
				if projW1(refl1(gamma)) <> refl2(projW1(gamma)) then
					return false;
				fi;
			od;
		od;
	od;
	return true;
end;

#### ---- Misc ----

# Prints all examples roots a, b, c and integers i, j > 1 with the following properties:
# - a and b are adjacent (i.e. a <> b and a <> -b and a+b is not a root, which implies that the crystallographic interval ]a,b[ is empty)
# - c + i*a + j*b is a root
# It does this first for F4 and then for G2 and then for A3. It turns out that no such examples exist.
findGradingCounterExample := function()
	local G2PosLC, G2RootsLC, A3PosLC, A3RootsLC, rootSys, a, b, c, i, j;
	G2PosLC := [ [1,0], [0,1], [1,1], [2,1], [3,1], [3,2] ];
	G2RootsLC := Concatenation(G2PosLC, -G2PosLC);
	A3PosLC := [ [1,0,0], [0,1,0], [0,0,1], [1,1,0], [0,1,1], [1,1,1] ];
	A3RootsLC := Concatenation(A3PosLC, -A3PosLC);
	for rootSys in [ F4RootsLC, G2RootsLC, A3RootsLC ] do
		# Display(rootSys);
		for a in rootSys do
			for b in rootSys do
				for c in rootSys do
					if not (a+b in rootSys) and a <> -b and a <> b then # a, b are adjacent
						for i in [ 2..4 ] do # Root strings have length at most 4
							for j in [ 2..4 ] do
								if  c+i*a+j*b in rootSys then
									Print(a, ", ", b, ", ", c, ", ", i, ", ", j, "\n");
								fi;
							od;
						od;
					fi;
				od;
			od;
		od;
	od;
end;
