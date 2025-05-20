InstallMethod(\*, "hijacked rat-fun * rat-fun", IsIdenticalObj, [IsRationalFunction, IsRationalFunction], 1000,
function(left, right)
	local fam, numRep, denRep, gcd, gcdRep, num2Rep, den2Rep;
	fam:=FamilyObj(left);
	if (HasIsZero(left) and IsZero(left)) or
		(HasIsZero(right) and IsZero(right)) then
		return Zero(fam);
	elif HasIsOne(left) and IsOne(left) then
		return right;
	elif HasIsOne(right) and IsOne(right) then
		return left;
	else
		numRep := ZippedProduct(
			ExtRepNumeratorRatFun(left), ExtRepNumeratorRatFun(right),
			fam!.zeroCoefficient, fam!.zippedProduct
		);
		denRep := ZippedProduct(
			ExtRepDenominatorRatFun(left), ExtRepDenominatorRatFun(right),
			fam!.zeroCoefficient, fam!.zippedProduct
		);
		if Length(denRep) = 2 and denRep[2][1] = [] and denRep[2][2] = fam!.oneCoefficient then
			return PolynomialByExtRepNC(fam, numRep);
		else
			return RationalFunctionByExtRep(fam, numRep, denRep);
		fi;
	fi;
end);
		# gcd := Gcd(PolynomialByExtRep(fam, numRep), PolynomialByExtRep(fam, denRep));
		# gcdRep := ExtRepPolynomialRatFun(gcd);
		# num2Rep := QuotientPolynomialsExtRep(fam, numRep, gcdRep);
		# den2Rep := QuotientPolynomialsExtRep(fam, denRep, gcdRep);