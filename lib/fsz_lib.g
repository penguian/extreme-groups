# FSZ_m test for a finite p-group, following Iovanov-Mason-Montgomery (Cor. 3.2) and Keilberg (Def. 1.1, 1.3):
#   G is FSZ_m  iff  |G_m(u,g)| = |G_m(u,g^n)| for all commuting u,g and all n coprime to |G|,
#   where G_m(u,g) = { a in G : a^m = (a u)^m = g }.
# It suffices to take u over conjugacy-class representatives (simultaneous conjugation is a bijection),
# and g over all m-th powers. g = 1 is trivial (g^n = g).
FSZTest := function(G, m)
  local elts, pw, W, H, Hg, cls, u, coef, h, i, g, k, ok, bad, ordg, j, gi;
  elts := AsList(G);
  pw := List(elts, x -> x^m);
  W := Set(Filtered(pw, x -> not IsOne(x)));           # nontrivial m-th powers
  H := Filtered([1..Length(elts)], i -> not IsOne(pw[i]));
  Hg := List(H, i -> Position(W, pw[i]));
  bad := [];
  for cls in ConjugacyClasses(G) do
    u := Representative(cls);
    coef := List(W, x -> 0);
    for j in [1..Length(H)] do
      h := elts[H[j]];
      if (h*u)^m = W[Hg[j]] then coef[Hg[j]] := coef[Hg[j]] + 1; fi;
    od;
    for gi in [1..Length(W)] do
      g := W[gi]; ordg := Order(g);
      for k in Filtered([2..ordg-1], k -> Gcd(k, ordg) = 1) do
        if coef[Position(W, g^k)] <> coef[gi] then
          Add(bad, [u, g, k, coef[gi], coef[Position(W, g^k)]]);
        fi;
      od;
    od;
  od;
  return bad;   # empty list <=> FSZ_m
end;

# Keilberg's S(p,1) = P x| <b>, P = Z_{p^2} x Z_p^{p-2}, a1 -> a1 a2^-1, ak -> ak a_{k+1}, a_{p-1} -> a_{p-1} a1^{-p}.
KeilbergS := function(p)
  local F, gens, b, a, rels, i, j, Q;
  F := FreeGroup(p);
  gens := GeneratorsOfGroup(F);
  b := gens[1]; a := gens{[2..p]};
  rels := [b^p, a[1]^(p^2)];
  for i in [2..p-1] do Add(rels, a[i]^p); od;
  for i in [1..p-1] do for j in [i+1..p-1] do Add(rels, Comm(a[i], a[j])); od; od;
  Add(rels, a[1]^b / (a[1]*a[2]^-1));
  for i in [2..p-2] do Add(rels, a[i]^b / (a[i]*a[i+1])); od;
  Add(rels, a[p-1]^b / (a[p-1]*a[1]^(-p)));
  Q := F / rels;
  return Image(EpimorphismPGroup(Q, p, 100));
end;
