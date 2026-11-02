# check_capable_extreme_7_9.g: are any of the capable groups of order 7^9 (below G(7,5)) extreme?
LoadPackage("anupq");
# Chain via the ANUPQ CapableDescendants option (agreed with mc-capable counts 9/29/20/0 at
# orders 7^7..7^10 in branch_depth_extreme.g); extremality test as in that script (k = 0..6).

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

Cap := G -> PqDescendants(G : StepSize := 1, CapableDescendants);
G3 := ExtraspecialGroup(343, 7);
S4 := Cap(G3)[1];
c5 := Cap(S4);
G75 := Filtered(c5, H -> not P1Abelian(H))[1];
g6 := Cap(G75)[1];
c7 := Cap(g6);   Print("capable 7^7: ", Length(c7), ", extreme among them: ", Number(c7, H -> IsExtremeGen(H, 7)), "\n");
c8 := Concatenation(List(c7, Cap));  Print("capable 7^8: ", Length(c8), "\n");
c9 := Concatenation(List(c8, Cap));  Print("capable 7^9: ", Length(c9), ", extreme among them: ", Number(c9, H -> IsExtremeGen(H, 7)), "\n");
