# klg_lib.g
# Library functions for Kovacs-Leedham-Green (KLG) positive Witt matrix groups
# G(p, m) inside UT(m+1, p) and conversion to polycyclic presentation (PcGroup).

if not IsBound(KLG_LIB_LOADED) then

Read("lib/extreme_lib.g");

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

KLG_LIB_LOADED := true;
fi;
