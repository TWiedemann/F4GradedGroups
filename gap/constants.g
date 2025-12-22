## ---- Bools ----
# If _SanitizeImmediately = true, DDSanitizeRep is applied after several transformations which
# may produce unsanitized (but correct) output
BindGlobal("_SanitizeImmediately", true);
# If true, the tests which check whether elements lie in ComRing or ConicAlg are skipped
BindGlobal("_SkipTests", false);
# If true, the values of ConicAlgMagTr are precomputed and cached.
BindGlobal("_CacheTrace", true);

# ---- Precomputed information ----
# Dictionary with precomputed values for all traces. Will be initalised later, mostly in init.g.
# _TrDict has as keys the representations of elements of ConicAlgMag and as objects their traces,
# which are elements of ComRing.
DeclareGlobalName("_TrDict");
# List with information about the indeterminates of ComRing in the order in which they
# appear in ComRing. I.e. _ComRingIndetInfo[i] contains information about the i-th indeterminate.
# Each entry is a list [ type, info ] where type is one of the strings "g", "t", "n", "tr"
# and info is additional information: For t_i and g_i, info is i. For n(x) and tr(x),
# info is x (as an element of ConicAlgMag)
DeclareGlobalName("_ComRingIndetInfo");
# _ComRingTraceIndets: List of all indeterminates of the form tr(a) \in ComRing with a \in ConicAlgMag.
# _ConicAlgTraces: List of the "corresponding" elements a+a' in ConicAlg.
# Used by WithoutTraces().
DeclareGlobalName("_ComRingTraceIndets");
DeclareGlobalName("_ConicAlgTraces");
# _TrSubIndetList contains trace indeterminates which may be replaced by other terms
# using the relation tr(xy') = tr(x)tr(y) - tr(xy). This relation may be used to replace
# all appearances of a_i' in tr.
# _TrSubValueList[i] is the term by which _TrSubIndetList[i] should be replaced.
DeclareGlobalName("_TrSubIndetList");
DeclareGlobalName("_TrSubValueList");

# ---- Misc ----
# The ring over which ComRing is a polynomial ring.
BindGlobal("ComRingBaseRing", Integers);
