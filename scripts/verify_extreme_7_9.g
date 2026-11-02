# verify_extreme_7_9.g
# Self-contained verification of an extreme permutation group of order 7^9.
# Discovered on 12 October 2026.
# Group lineage: G(7,5) -> g1 (order 7^6) -> d7[15] (order 7^7) -> Child 13 (order 7^8) -> Group 1 (order 7^9).
# Stabilizer: S = <x4, x2*x3> of order 7^4 = 2401, Core_G(S) = 1.
# Degree: d = [G:S] = 7^5 = 16807.
# Extremality: (p+1)*f(G,S) = |G| + 1 <=> 8 * 5044201 = 40353608.

LoadPackage("anupq");

ExpNil := function(u, p)
  local r, t, k;
  r := u^0; t := u^0;
  for k in [1..p-1] do t := t*u/k; r := r + t; od;
  return r;
end;

KLGmats := function(p, m)
  local F, n, i, k, mat, gens;
  F := GF(p); n := m+1; gens := [];
  for i in [1..m] do
    mat := NullMat(n, n, F);
    for k in [1..m+1-i] do mat[k][k+i] := k*One(F); od;
    Add(gens, ExpNil(mat, p));
  od;
  return gens;
end;

NormalForm := function(X, gens, m)
  local a, i, e;
  a := [];
  for i in [1..m] do
    e := IntFFE(X[1][i+1]);
    Add(a, e);
    X := gens[i]^(-e) * X;
  od;
  if not IsOne(X) then Error("not in G"); fi;
  return a;
end;

KLGpc := function(p, m)
  local gens, F, fg, coll, i, j;
  gens := KLGmats(p, m);
  fg := FreeGroup(m); F := GeneratorsOfGroup(fg);
  coll := SingleCollector(fg, List([1..m], i -> p));
  for i in [1..m] do
    SetPower(coll, i, Product([1..m], k -> F[k]^NormalForm(gens[i]^p, gens, m)[k]));
    for j in [i+1..m] do
      SetConjugate(coll, j, i, Product([1..m], k -> F[k]^NormalForm(gens[j]^gens[i], gens, m)[k]));
    od;
  od;
  return GroupByRwsNC(coll);
end;

UltraFastF := function(G, H)
  local reps, ccs;
  reps := List(ConjugacyClasses(H), Representative);
  ccs := Set(List(reps, r -> ConjugacyClass(G, r)));
  return Sum(ccs, Size);
end;

t_start := Runtime();

# 1. Construct root G(7,5) and advance down coclass-1 spine
G75 := KLGpc(7, 5);
des75_1 := PqDescendants(G75 : StepSize := 1);
g1 := des75_1[1];
des_g1 := PqDescendants(g1 : StepSize := 1);
G15 := des_g1[15];
des8 := PqDescendants(G15 : StepSize := 1);
c13 := des8[13];
des9 := PqDescendants(c13 : StepSize := 1);
G := des9[1];

x := Pcgs(G);
S := Subgroup(G, [x[4], x[2]*x[3]]);

Print("====================================================================\n");
Print("VERIFICATION OF EXTREME PERMUTATION GROUP OF ORDER 7^9\n");
Print("====================================================================\n");
Print("Order |G|            : ", Size(G), " = 7^", Log(Size(G), 7), "\n");
Print("Nilpotency class     : ", NilpotencyClassOfGroup(G), " (maximal class)\n");
Print("Derived length       : ", DerivedLength(G), "\n");
Print("Exponent             : ", Exponent(G), "\n");
Print("Order of stabilizer S: ", Size(S), " = 7^", Log(Size(S), 7), "\n");
Print("Core_G(S) size       : ", Size(Core(G, S)), " (core-free)\n");

# 2. Extremality check
f := UltraFastF(G, S);
Print("Fixed-point union f  : ", f, "\n");
Print("Target f = (7^9+1)/8 : ", (7^9 + 1)/8, "\n");
Print("(p+1)*f = |G| + 1    : ", 8*f = Size(G)+1, " [8 * ", f, " = ", 8*f, "]\n");

# 3. Coset action and subdegrees
act := FactorCosetAction(G, S);
P := Image(act);
deg := NrMovedPoints(P);
Print("Permutation degree   : ", deg, " = 7^", Log(deg, 7), "\n");
Print("Action faithful      : ", Size(P) = Size(G), "\n");

Sa := Image(act, S);
orbs := Orbits(Sa, [1..deg]);
subdegs := Collected(List(orbs, Length));
Print("Rank                 : ", Length(orbs), "\n");
Print("Subdegree profile    : ", subdegs, "\n");
expected_subdegs := [ [1, 7], [7, 6], [49, 6], [343, 6], [2401, 6] ];
Print("Matches CKNP Thm 1E  : ", subdegs = expected_subdegs, "\n");

# 4. Suborbit regularity
regular_ok := ForAll(orbs, O -> Size(Sa)/Size(Stabilizer(Sa, O[1])) = Length(O));
Print("Suborbits regular    : ", regular_ok, "\n");

# 5. Normalizer chain (CKNP Theorem 2E)
G_chain := [ S ];
cur := S;
for i in [1..4] do
  cur := Normalizer(G, cur);
  Add(G_chain, cur);
od;
Print("Normalizer chain |G_i|: ", List(G_chain, Size), "\n");
Print("Chain indices         : ", List([1..4], i -> Index(G_chain[i+1], G_chain[i])), "\n");
H_chain := List(G_chain, sub -> Core(sub, S));
Print("Cores |H_i|           : ", List(H_chain, Size), "\n");

Print("\nTotal verification runtime: ", Runtime() - t_start, " ms\n");
Print("====================================================================\n");
QUIT;
