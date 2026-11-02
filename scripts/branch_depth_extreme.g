# branch_depth_extreme.g   (revised 17 Oct 2026)
# Branch/depth audit of extreme maximal-class p-groups in the coclass tree T(p), p = 3, 5, 7.
# Conventions (Dietrich 2010, J. Group Theory 13, 851-871): S_n = mainline group of order p^n;
# B_n = descendants of S_n that are not descendants of S_{n+1}; depth of H of order p^m in B_n is m-n.
# "Capable" here = has an immediate descendant of maximal class (class n for order p^n), called
# mc-capable.  This is NOT always the same as ANUPQ's CapableDescendants option (p-class based);
# see the comparison printed for p = 5.
# Everything printed below is computed; nothing is hard-coded except the expected values in checks.
LoadPackage("anupq");

UltraFastF := function(G, H)
  local reps, ccs;
  reps := List(ConjugacyClasses(H), Representative);
  ccs := Set(List(reps, r -> ConjugacyClass(G, r)));
  return Sum(ccs, Size);
end;

McChildren := function(G, n)   # maximal-class immediate descendants of G (|G| = p^n)
  return Filtered(PqDescendants(G : StepSize := 1), H -> NilpotencyClassOfGroup(H) = n);
end;
IsMcCapable := G -> Length(McChildren(G, LogInt(Size(G), PrimeDivisors(Size(G))[1]))) > 0;

# P_1 = C_G(gamma_2/gamma_4); S_n has abelian P_1.
P1Abelian := function(G)
  local L, h, C;
  L := LowerCentralSeries(G);
  h := NaturalHomomorphismByNormalSubgroup(G, L[4]);
  C := Centralizer(Image(h), Image(h, L[2]));
  return IsAbelian(PreImage(h, C));
end;
# Quotient of order p^5: G/gamma_5(G).
Quot5 := function(G)
  return Image(NaturalHomomorphismByNormalSubgroup(G, LowerCentralSeries(G)[5]));
end;

# Extremality test: some core-free S of order p^(n-1), S = <x4, x2*x3^k> (k = 0..p-1), with
# (p+1)*f(G,S) = |G|+1 (same family of S as classify_extreme_5_5_to_5_9.g; for p = 7 the earlier
# script used k = 0 only).  For p = 3 (order 3^5) a full search over subgroup classes is used.
IsExtremeGen := function(G, p)
  local x, m, n, S, k, c;
  m := LogInt(Size(G), p); n := (m + 1) / 2;
  if p = 3 then
    for c in ConjugacyClassesSubgroups(G) do
      S := Representative(c);
      if Size(S) = p^(n-1) and Size(Core(G, S)) = 1
         and UltraFastF(G, S) = (p^m + 1) / (p + 1) then return true; fi;
    od;
    return false;
  fi;
  x := Pcgs(G);
  for k in [0..p-1] do
    S := Subgroup(G, [x[4], x[2] * x[3]^k]);
    if Size(S) = p^(n-1) and not (x[m] in S) and UltraFastF(G, S) = (p^m + 1) / (p + 1) then
      return true;
    fi;
  od;
  return false;
end;

# Common start: mainline up to order p^4, then split at p^5 by abelian P_1.
Start := function(p)
  local G3, S4, d5, cap5, S5, G5;
  G3 := ExtraspecialGroup(p^3, p);
  S4 := Filtered(McChildren(G3, 3), H -> IsMcCapable(H))[1];
  d5 := McChildren(S4, 4);
  cap5 := Filtered(d5, IsMcCapable);
  S5 := Filtered(cap5, P1Abelian);
  G5 := Filtered(cap5, H -> not P1Abelian(H));
  Print("p = ", p, ": order p^4 capable groups: ", Number(McChildren(G3, 3), IsMcCapable),
        "; order p^5 mc groups: ", Length(d5), ", capable: ", Length(cap5),
        ", capable with abelian P_1 (mainline S_5): ", Length(S5),
        ", capable with non-abelian P_1: ", Length(G5), "\n");
  return rec(S4 := S4, S5 := S5[1], G5 := G5, d5 := d5);
end;

Print("====================================================================\n");
Print("BRANCH AND DEPTH AUDIT OF EXTREME MAXIMAL-CLASS GROUPS (p = 3, 5, 7)\n");
Print("====================================================================\n\n");

# ---------------- p = 5 ----------------
Print("--- p = 5 ---\n");
r := Start(5);
E5 := r.G5[1];
d6 := McChildren(E5, 5);  cap6 := Filtered(d6, IsMcCapable);
Print("E5: ", Length(d6), " children at 5^6, ", Length(cap6), " capable\n");
g6 := cap6[1];
d7 := McChildren(g6, 6);
ext7 := Filtered([1..Length(d7)], i -> IsExtremeGen(d7[i], 5));
cap7 := Filtered([1..Length(d7)], i -> IsMcCapable(d7[i]));
Print("5^7: ", Length(d7), " groups, ", Length(ext7), " extreme, mc-capable indices ", cap7,
      ", capable AND extreme: ", Intersection(ext7, cap7), "\n");
Print("  extreme groups with G/gamma_5 of non-abelian P_1: ",
      Number(ext7, i -> not P1Abelian(Quot5(d7[i]))), " of ", Length(ext7), "\n");
Print("  CapableDescendants (ANUPQ option) from g6: ",
      Length(PqDescendants(g6 : StepSize := 1, CapableDescendants)),
      " vs mc-capable: ", Length(cap7), "\n");
lvl := List(cap7, i -> d7[i]);
for n in [7, 8] do
  kids := Concatenation(List(lvl, H -> McChildren(H, n)));
  cp := Filtered(kids, IsMcCapable);
  Print("5^", n+1, ": ", Length(kids), " groups below capable 5^", n, " groups, ", Length(cp), " capable\n");
  lvl := cp;
od;

# ---------------- p = 7 ----------------
Print("\n--- p = 7 ---\n");
r := Start(7);
G75 := r.G5[1];
d6 := McChildren(G75, 5);  cap6 := Filtered(d6, IsMcCapable);
Print("G(7,5): ", Length(d6), " children at 7^6, ", Length(cap6), " capable\n");
g6 := cap6[1];
d7 := McChildren(g6, 6);
ext7 := Filtered([1..Length(d7)], i -> IsExtremeGen(d7[i], 7));
cap7 := Filtered([1..Length(d7)], i -> IsMcCapable(d7[i]));
Print("7^7: ", Length(d7), " groups, ", Length(ext7), " extreme, mc-capable indices ", cap7,
      ", capable AND extreme: ", Intersection(ext7, cap7), "\n");
Print("  extreme groups with G/gamma_5 of non-abelian P_1: ",
      Number(ext7, i -> not P1Abelian(Quot5(d7[i]))), " of ", Length(ext7), "\n");
lvl := List(cap7, i -> d7[i]);
for n in [7, 8, 9] do
  kids := Concatenation(List(lvl, H -> McChildren(H, n)));
  cp := Filtered(kids, IsMcCapable);
  Print("7^", n+1, ": ", Length(kids), " groups below capable 7^", n, " groups, ", Length(cp), " capable\n");
  lvl := cp;
od;

# ---------------- p = 3 ----------------
Print("\n--- p = 3 (outside the p >= 5 argument; shown for completeness) ---\n");
G3 := ExtraspecialGroup(27, 3);
S4 := Filtered(McChildren(G3, 3), IsMcCapable);
Print("3^4 capable groups: ", Length(S4), "\n");
d5 := McChildren(S4[1], 4);
ext5 := Filtered(d5, H -> IsExtremeGen(H, 3));
Print("3^5: ", Length(d5), " groups, ", Length(ext5), " extreme, of which capable: ",
      Number(ext5, IsMcCapable), "\n");
Print("====================================================================\n");
