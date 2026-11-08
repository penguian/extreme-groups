# klg_lib.g
# Library functions for Kovacs-Leedham-Green (KLG) positive Witt matrix groups
# G(p, m) inside UT(m+1, p), conversion to polycyclic presentation (PcGroup),
# and fast computation of the fixed-point union size f(G, H) = |\bigcup_{g in G} H^g|.

# Truncated exponential series sum_{k=0}^{p-1} u^k / k! for a nilpotent matrix u with u^p = 0.
ExpNil := function(u, p)
  local r, t, k;
  r := u^0;
  t := u^0;
  for k in [1..p-1] do
    t := t * u / k;
    r := r + t;
  od;
  return r;
end;

# Generators exp(u_1), ..., exp(u_m) of the KLG group G(p, m) <= UT(m+1, F_p),
# where (u_i)_{k, k+i} = k for 1 <= k <= m + 1 - i.
KLGmats := function(p, m)
  local F, n, i, k, mat, gens;
  F := GF(p);
  n := m + 1;
  gens := [];
  for i in [1..m] do
    mat := NullMat(n, n, F);
    for k in [1..m+1-i] do
      mat[k][k+i] := k * One(F);
    od;
    Add(gens, ExpNil(mat, p));
  od;
  return gens;
end;

# Unique exponent vector [a_1, ..., a_m] in {0..p-1}^m such that
# X = gens[1]^a_1 * ... * gens[m]^a_m in G(p, m).
NormalForm := function(X, gens, m)
  local a, i, e;
  a := [];
  for i in [1..m] do
    e := IntFFE(X[1][i+1]);
    Add(a, e);
    X := gens[i]^(-e) * X;
  od;
  if not IsOne(X) then
    Error("Matrix X does not lie in G(p, m)");
  fi;
  return a;
end;

# Construct G(p, m) as a polycyclic group (PcGroup) via its collector on gens[1..m].
KLGpc := function(p, m)
  local gens, F, fg, coll, i, j, nf;
  gens := KLGmats(p, m);
  fg := FreeGroup(m);
  F := GeneratorsOfGroup(fg);
  coll := SingleCollector(fg, List([1..m], i -> p));
  for i in [1..m] do
    nf := NormalForm(gens[i]^p, gens, m);
    SetPower(coll, i, Product([1..m], k -> F[k]^nf[k]));
    for j in [i+1..m] do
      nf := NormalForm(gens[j]^gens[i], gens, m);
      SetConjugate(coll, j, i, Product([1..m], k -> F[k]^nf[k]));
    od;
  od;
  return GroupByRwsNC(coll);
end;

# Compute f(G, H) = |\bigcup_{g in G} H^g|, the number of elements of G fixing at least
# one point in the coset action of G on G/H, as the sum of sizes of the distinct
# G-conjugacy classes intersecting H.
#
# Implementation note on deduplicating G-conjugacy classes:
# - For |G| <= 5^9, H may be abelian of order 625 (up to 625 classes in H), while
#   conjugacy classes in G are small, so sorting via Set(...) (which orders classes
#   by RepresentativeSmallest) is fast and O(k log k).
# - For |G| > 5^9 (e.g. |G| = 7^9 = 40,353,607), non-central G-classes have size up to
#   7^7 = 823,543, making RepresentativeSmallest expensive (~200 ms/class), whereas
#   the non-abelian stabilizer H of order 7^4 has only 97 conjugacy classes. Testing
#   class membership (r in pair[1]) among classes of matching size avoids
#   RepresentativeSmallest and is >30x faster at 7^9.
UltraFastF := function(G, H)
  local reps, kept, r, cc, sz;
  reps := List(ConjugacyClasses(H), Representative);
  if Size(G) <= 5^9 then
    return Sum(Set(List(reps, r -> ConjugacyClass(G, r))), Size);
  fi;
  kept := [];
  for r in reps do
    cc := ConjugacyClass(G, r);
    sz := Size(cc);
    if not ForAny(kept, pair -> pair[2] = sz and r in pair[1]) then
      Add(kept, [cc, sz]);
    fi;
  od;
  return Sum(kept, pair -> pair[2]);
end;

# Two-step centralizer P_1(G) = G_1 = C_G(gamma_2(G) / gamma_4(G)) of a maximal-class p-group G.
TwoStepCentralizer := function(G)
  local L, pi;
  L := LowerCentralSeriesOfGroup(G);
  pi := NaturalHomomorphismByNormalSubgroup(G, L[4]);
  return PreImage(pi, Centralizer(Image(pi, G), Image(pi, L[2])));
end;

# Test whether the two-step centralizer P_1(G) is abelian (true on the coclass-1 mainline S_n).
P1Abelian := G -> IsAbelian(TwoStepCentralizer(G));
