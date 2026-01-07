### This file contains the definition of ConicAlg, a free nonassociative algebra
### that represents an arbitrary multiplicative conic alternative algebra,
### and functions related to it.
### Technically, ConicAlg is a free magma ring over the free magma ConicAlgMag
### whose coefficient ring is ComRing.

# ----- Definition of ConicAlg -----

BindGlobal("ConicAlg", FreeMagmaRing(ComRing, ConicAlgMag));

BindGlobal("ConicAlgMagEmb", x -> ImageElm(Embedding(ConicAlgMag, ConicAlg), x));


# ----- Functions which test requirements and throw errors ---

DeclareOperation("ReqComRingEl", [IsRingElement]);
DeclareOperation("ReqComRingEl", [IsList]);
DeclareOperation("ReqConicAlgEl", [IsRingElement]);
DeclareOperation("ReqConicAlgEl", [IsList]);

# For runtime reasons, we only test whether an element is a rational function
# to determine whether it lies (or rather, can possibly lie) in ComRing.
# Since these functions are essentially only a safeguard against inputting
# elements of ConicAlg where elements of ComRing are required (and vice versa),
# this is sufficient.

InstallMethod(ReqComRingEl, [IsRingElement], function(a)
	if _SkipTests then
		return true;
	fi;
	# We only test
	if not IsRationalFunction(a) then
		Display(a);
		Error("Invalid input: Must be in ComRing.");
		return false;
	fi;
	return true;
end);
InstallMethod(ReqComRingEl, [IsList], function(list)
	local a;
	for a in list do
		if not ReqComRingEl(a) then
			return false;
		fi;
	od;
	return true;
end);

InstallMethod(ReqConicAlgEl, [IsRingElement], function(a)
	if _SkipTests then
		return true;
	fi;
	if not a in ConicAlg then
		Display(a);
		Error("Invalid input: Must be in ConicAlg.");
		return false;
	fi;
	return true;
end);
InstallMethod(ReqConicAlgEl, [IsList], function(list)
	local a;
	for a in list do
		ReqConicAlgEl(a);
	od;
end);

# ----- Constructors for indeterminates -----

BindGlobal("ConicAlgIndet", function(i)
	return ConicAlgMagEmb(ConicAlgMagIndet(i));
end);

BindGlobal("ConicAlgInvIndet", function(i)
	return ConicAlgMagEmb(ConicAlgMagInvIndet(i));
end);

# ----- Conjugation, trace, norm on ConicAlg -----

# a: Element of ConicAlg.
# Returns: The conjugate a' of a.
BindGlobal("ConicAlgInv", function(a)
	ReqConicAlgEl(a);
	return ChangeRingElByMagmaTrans(ConicAlg, a, ConicAlgMagInv);
end);

# magFunc: A function ConicAlgMag -> ComRing.
# Returns: The linear extension ConicAlg -> Comring of magFunc.
BindGlobal("ConicAlgFunctionalFromMagFunctional", function(magFunc)
	return function(a)
		local coeffList, result, i, magmaEl, coeff;
		coeffList := CoefficientsAndMagmaElements(a);
		result := Zero(ComRing);
		for i in [1..Length(coeffList)/2] do
			magmaEl := coeffList[2*i - 1]; # \in ConicAlgMag
			coeff := coeffList[2*i]; # \in ComRing
			result := result + coeff * magFunc(magmaEl);
		od;
		return result;
	end;
end);

BindGlobal("ConicAlgTr", ConicAlgFunctionalFromMagFunctional(ConicAlgMagTr));

# a, b: Elements of ConicAlg.
# Returns: n(a,b) := n(a+b) - n(a) - n(b).
# By [GPR24, (16.12.4), (16.5.2)], we have n(a,b) = n(1, a'b) = t(a'b)
BindGlobal("ConicAlgNormLin", function(a, b)
	ReqConicAlgEl([a,b]);
	return ConicAlgTr(ConicAlgInv(a)*b);
end);

# a: Element of ConicAlg.
# Returns: Its norm n(a), an element of ComRing.
# Use that n(\sum_i c_i m_i) = \sum_i c_i^2 n(m_i) + sum_{i<j} c_i c_j n(m_i, m_j)
BindGlobal("ConicAlgNorm", function(a)
	local coeffList, result, i, j, magmaEl, magmaEl2, coeff, coeff2;
	ReqConicAlgEl(a);
	coeffList := CoefficientsAndMagmaElements(a);
	result := Zero(ComRing);
	for i in [1..Length(coeffList)/2] do
		magmaEl := coeffList[2*i - 1]; # \in ConicAlgMag
		coeff := coeffList[2*i]; # \in ComRing
		# a is the sum of all coeff*magmaEl. Begin by adding coeff^2 * n(magmaEl).
		result := result + coeff^2 * ConicAlgMagNorm(magmaEl); # norm(x_i)
		for j in [i+1..Length(coeffList)/2] do
			magmaEl2 := coeffList[2*j - 1]; # \in ConicAlgMag
			coeff2 := coeffList[2*j]; # \in ComRing

			result := result + coeff*coeff2 * ConicAlgMagNormLin(magmaEl, magmaEl2); # tr(x_i x_j') = linearisation of norm
		od;
	od;
	return result;
end);

# ----- Shortcuts for conjugation, trace, norm on ConicAlg OR ConicAlgMag -----

# a: Element of ConicAlgMag or of ConicAlg
# Returns: a'
BindGlobal("ConicInv", function(a)
	if a in ConicAlg then
		return ConicAlgInv(a);
	elif a in ConicAlgMag then
		return ConicAlgMagInv(a);
	else
		return fail;
	fi;
end);

# a: Element of ConicAlgMag or of ConicAlg
# Returns: tr(a) \in ComRing
BindGlobal("ConicTr", function(a)
	if a in ConicAlg then
		return ConicAlgTr(a);
	elif a in ConicAlgMag then
		return ConicAlgMagTr(a);
	else
		return fail;
	fi;
end);

# a: Element of ConicAlgMag or of ConicAlg
# Returns: n(a) \in ComRing
BindGlobal("ConicNorm", function(a)
	if a in ConicAlg then
		return ConicAlgNorm(a);
	elif a in ConicAlgMag then
		return ConicAlgMagNorm(a);
	else
		return fail;
	fi;
end);

# a,b: Element of ConicAlgMag or of ConicAlg (both in the same)
# Returns: n(a,b) \in ComRing
BindGlobal("ConicNormLin", function(a,b)
	if a in ConicAlg and b in ConicAlg then
		return ConicAlgNormLin(a,b);
	elif a in ConicAlgMag and b in ConicAlgMag then
		return ConicAlgMagNormLin(a,b);
	else
		return fail;
	fi;
end);

# ----- Misc functions -----

# a: Element of ConicAlg.
# Returns: [t, b] with t \in ComRing, b \in ConicAlg such that a = t*One(ConicAlg)+b
# and such that b has no summand of the form s*One(ConicAlg) for s \in ComRing
BindGlobal("ConicAlgSplitOne", function(a)
	local coeffList, i, magEl, t;
	coeffList := CoefficientsAndMagmaElements(a);
	# Look for summand t*One(ConicAlg)
	for i in [1..Length(coeffList)/2] do
		magEl := coeffList[2*i-1];
		if magEl = One(ConicAlgMag) then
			# Summand t*One(ConicAlg) found
			t := coeffList[2*i];
			return [t, a - t*One(ConicAlg)];
		fi;
	od;
	# No summand t*One(ConicAlg) found
	return [Zero(ComRing), a];
end);

# twist: Element of the twisting group of (ComRing, ConicAlg), i.e., one of
# [1,1], [-1,1], [1,-1], [-1,-1].
# a: Element of ComRing or of ConicAlg.
# Returns: twist.a, i.e., the action of twist on a.
BindGlobal("TwistGrpAct", function(twist, a)
	if IsRationalFunction(a) then # a in ComRing
		return twist[1]*a;
	else
		a := twist[1]*a;
		if twist[2] = -1 then
			a := ConicAlgInv(a);
		fi;
		return a;
	fi;
end);
