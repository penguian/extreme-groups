# Clean library functions for KLG groups and fast fixed-point computation

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
