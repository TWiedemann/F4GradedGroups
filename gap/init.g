### This file calls functions that initialise
### _ComRingTraceIndets, _ConicAlgTraces, _TrSubIndetList and _TrSubValueList.
### For their documentation, see read.g.
### The list _ComRingIndetInfo and the dict _TrDict are not initialised here but in comring.g
### because _InitTrDict has to be called before ComRing is defined.

# Initialises the lists _ComRingTraceIndets and _ConicAlgTraces
_InitTraceIndets := function()
	local i, infoList, type, info, a, aInv;
	_ComRingTraceIndets := [];
	_ConicAlgTraces := [];
	# Look up the corresponding information in _ComRingIndetInfo
	for i in [1..Length(_ComRingIndetInfo)] do
		infoList := _ComRingIndetInfo[i];
		type := infoList[1];
		info := infoList[2];
		if type = "tr" then
			Add(_ComRingTraceIndets, Indeterminate(BaseRing, i));
			a := ConicAlgMagEmb(info); # \in ConicAlg
			aInv := ConicAlgMagEmb(ConicAlgMagInv(a));
			Add(_ConicAlgTraces, a+ConicAlgInv(a));
		fi;
	od;
end;

_InitTraceIndets();

# Initialises the lists _TrSubIndetList and _TrSubValueList
# Currently these lists are filled "by hand" and only for products tr(xyz) up
# to length 3. This is sufficient for our computations.
_InitTrSubLists := function()
	local tr, inv, add, indet, i, j, k, x, y, z;
	_TrSubIndetList := [];
	_TrSubValueList := [];
	tr := ConicAlgMagTr;
	inv := ConicAlgMagInv;
	indet := ConicAlgMagIndet;
	# trace: Element of ConicAlgMag.
	# value: Element of ConicAlg.
	# Adds trace and value to the desired lists.
	add := function(trace, value)
		if trace in _ComRingTraceIndets and not trace in _TrSubIndetList then
			Add(_TrSubIndetList, trace);
			Add(_TrSubValueList, value);
		fi;
	end;
	for i in [1..ConicAlg_rank] do
		for j in [1..ConicAlg_rank] do
			x := indet(i);
			y := indet(j);
			## Product of length 2
			# tr(xy') = tr(x)tr(y) - tr(xy)
			add(tr(x*inv(y)), tr(x)*tr(y) - tr(x*y));
			## Products of length 3
			for k in [1..ConicAlg_rank] do
				z := indet(k);
				# tr(xyz') = tr(xy)tr(z) - tr(xyz)
				add(tr(x*y*inv(z)), tr(x*y)*tr(z) - tr(x*y*z));
				# tr(x'yz) = tr(x)tr(yz) - tr(xyz)
				add(tr(inv(x)*y*z), tr(x)*tr(y*z) - tr(x*y*z));
				# tr(xy'z) = tr(zxy') = tr(zx)tr(y) - tr(zxy)
				add(tr(x*inv(y)*z), tr(z*x)*tr(y) - tr(z*x*y));
				# tr(x'y'z) = tr(z'yx) = tr(z)tr(yx) - tr(zyx)
				add(tr(inv(x)*inv(y)*z), tr(z)*tr(y*x) - tr(z*y*x));
				# tr(x'yz') = tr(zy'x) = tr(xz)tr(y) - tr(xzy)
				add(tr(inv(x)*y*inv(z)), tr(x*z)*tr(y) - tr(x*z*y));
				# tr(xy'z') = tr(zyx') = tr(x)tr(yz) - tr(xzy)
				add(tr(x*inv(y)*inv(z)), tr(x)*tr(y*z) - tr(x*z*y));
			od;
		od;
	od;
end;

_InitTrSubLists();