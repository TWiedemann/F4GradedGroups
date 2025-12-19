### This file contains the definition of the [0,0]-part of the Lie algebra,
### also called Z in [DMW]. We refer to it as DD.
### It is the ComRing-span of all dd_{a,b} for a, b \in Cubic.

### Internal representation:
# An element t1 * dd_{a1, b1} + t2 * dd_{a2, b2} + ... is represented by
# the list [[t1, a1, b2], [t2, a2, b2], ...].

# ----- Definition and internal representation -----

# rep: Representation of an element of DD.
# Returns: Nothing, but the following sanitization steps are applied to rep:
# - Summands c*dd_{a,b} with one of a, b, c equal to zero are removed
# - If two summands c1*dd_{a,b}, c2*dd_{a,b} appear, they are replaced by (c1+c2)*dd_{a,b}
DDSanitizeRep := function(rep)
	local i, j, x;
	for i in [Length(rep), Length(rep)-1 .. 1] do
		if i > Length(rep) then
			# This may happen because we remove elements from rep during the loop
			continue;
		fi;
		x := rep[i];
		# Remove zero summands
		if IsZero(x[1]) or IsZero(x[2]) or IsZero(x[3]) then
			Remove(rep, i);
			continue;
		fi;
		# Merge summands
		for j in [1..i-1] do
			if rep[j][2] = x[2] and rep[j][3] = x[3] then
				rep[j][1] := rep[j][1] + x[1];
				Remove(rep, i);
				if rep[j][1] = Zero(ComRing) then
					Remove(rep, j);
				fi;
				break;
			fi;
		od;
	od;
end;

# Display strings
_DDZeroString := "0_{DD}";
_DDSymString := "\dd";

# a: Internal representation of an element of DD.
# Returns: A string representation of a.
DDRepToString := function(a)
	local stringList, summand, s;
	stringList := [];
	for summand in a do
		s := Concatenation(_DDSymString, "_{", String(summand[2]), ",", String(summand[3]), "}");
		if summand[1] <> One(ComRing) then
			s := Concatenation("(", String(summand[1]), ")", "*", s); 
		fi;
		Add(stringList, s);
	od;
	return StringSum(stringList, "+", _DDZeroString);
end;

DDSpec := rec(
	ElementName := "DDElement",
	Zero := a -> [],
	Addition := function(a, b)
		local sum;
		# We have to copy a and b: Otherwise DDSanitizeRep(sum) will change
		# a and b as well, which would be horrible
		sum := Concatenation(StructuralCopy(a),StructuralCopy(b));
		if _SanitizeImmediately then
			DDSanitizeRep(sum);
		fi;
		return sum;
	end,
	AdditiveInverse := function(a)
		local inv, i;
		inv := [];
		for i in [1..Length(a)] do
			Add(inv, [-a[i][1], a[i][2], a[i][3]]);
		od;
		return inv;
	end,
	Print := function(a)
		Print(DDRepToString(a));
	end,
	# Lie bracket on DD
	Multiplication := function(a, b)
		local productRep, summand1, summand2, x1, x2, y1, y2, z1, z2, coeff;
		# We do not sanitize the input because, under normal circumstances, it should already
		# be sanitized
		productRep := [];
		for summand1 in a do
			x1 := summand1[2];
			x2 := summand1[3];
			for summand2 in b do
				y1 := summand2[2];
				y2 := summand2[3];
				# summand1*summand2 = coeff * (dd_{D_{x1,x2}(y1), y2} - dd_{y1, D_{x2,x1}(y2)})
				# Here "D" is JordanD
				coeff := summand1[1] * summand2[1]; # in ComRing
				z1 := JordanD(x1, x2, y1);
				z2 := y2;
				if not IsZero(z1) then
					Add(productRep, [coeff, z1, z2]);
				fi;
				z1 := y1;
				z2 := JordanD(x2, x1, y2);
				if not IsZero(z2) then
					Add(productRep, [-coeff, z1, z2]);
				fi;
			od;
		od;
		if _SanitizeImmediately then
			DDSanitizeRep(productRep);
		fi;
		return productRep;
	end,
	MathInfo := IsAdditivelyCommutativeElement
);

DD := ArithmeticElementCreator(DDSpec);
InstallMethod(String, [IsDDElement], x -> DDRepToString(UnderlyingElement(x)));

# Scalar multiplication ComRing x DD -> DD
InstallOtherMethod(\*, "for ComRingElement and DDElement", [IsRingElement, IsDDElement], 2, function(comEl, ddEl)
	local resultRep, summand;
    ReqComRingEl(comEl);
    resultRep := [];
    for summand in UnderlyingElement(ddEl) do
        Add(resultRep, [comEl*summand[1], summand[2], summand[3]]);
    od; 
	return DD(resultRep);
end);

# ----- Getter functions for internal representation of DD -----
DeclareOperation("DDCoeffList", [IsDDElement]);

# ddEl: c1*dd_{a1,b1} + c2*dd_{a2,b2} + ... \in DD
# Returns: [[c1, a1, b1], [c2, a2, b2], ...]
InstallMethod(DDCoeffList, [IsDDElement], function(ddEl)
	return UnderlyingElement(ddEl);
end);

# ----- Constructors for elements of DD -----

DDZero := DD([]);

# cubicEl1, cubicEl2: Elements of Cubic.
# Returns: dd_{cubicEl1, cubicEl2} \in DD.
DeclareOperation("DDdd", [IsCubicElement, IsCubicElement]);
InstallMethod(DDdd, [IsCubicElement, IsCubicElement], function(cubicEl1, cubicEl2)
	if IsZero(cubicEl1) or IsZero(cubicEl2) then
		return DDZero;
	else
		return DD([[One(ComRing), cubicEl1, cubicEl2]]);
	fi;
end);

DeclareOperation("DDElFromCoeffList", [IsList]);
InstallMethod(DDElFromCoeffList, [IsList], function(coeffList)
	return DD(coeffList);
end);
