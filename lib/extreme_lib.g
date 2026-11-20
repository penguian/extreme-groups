# extreme_lib.g
# Shared core utilities for extreme transitive p-groups of maximal class:
# package loading, fast fixed-point counting, two-step centralizers,
# maximal-class descendant helpers, ANUPQ weighted p-quotient alignment,
# normalizer-core towers, and tilted-stabilizer searches.

if not IsBound(EXTREME_LIB_LOADED) then

# Load a required GAP package and fail loudly if unavailable.
RequirePackage := function(name)
  if LoadPackage(name) = fail then
    Error("Required GAP package '", name, "' could not be loaded");
  fi;
end;

# Extremal fixed-point union size f = (p^m + 1) / (p + 1) for odd m.
ExtremeTargetF := function(p, m)
  return (p^m + 1) / (p + 1);
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

# Test whether G is a p-group of maximal class (nilpotency class log_p(|G|) - 1).
IsMaximalClassPGroup := function(G, p)
  return NilpotencyClassOfGroup(G) = LogInt(Size(G), p) - 1;
end;

# Maximal-class immediate descendants of G (target nilpotency class n for |G| = p^n).
MaxClassChildren := function(G, n)
  return Filtered(ValueGlobal("PqDescendants")(G : StepSize := 1), H -> NilpotencyClassOfGroup(H) = n);
end;

# Capable immediate descendants of maximal class (ANUPQ's CapableDescendants restricts p-class,
# which captures all groups having a maximal-class immediate descendant).
MaxClassCapableChildren := function(G, n)
  return Filtered(ValueGlobal("PqDescendants")(G : StepSize := 1, CapableDescendants),
                  H -> NilpotencyClassOfGroup(H) = n);
end;

# Test whether G has at least one immediate descendant of maximal class.
IsMcCapable := G -> Length(MaxClassChildren(G, LogInt(Size(G), PrimeDivisors(Size(G))[1]))) > 0;

# Re-encode a p-group G into ANUPQ's weighted p-quotient PcGroup via Pq(...).
# In ANUPQ <= 3.3.3 (prior to upstream gap-packages/anupq PR #96), PQ_DESCENDANTS
# passes PcgsPCentralSeriesPGroup(G) directly in PQ_AUT_INPUT while pq re-derives its
# own internal weighted pcp; pre-computing Pq(...) aligns the two bases cleanly.
PqWeightedPresentation := function(G, p)
  local m;
  m := LogInt(Size(G), p);
  return ValueGlobal("Pq")(G : Prime := p, ClassBound := m - 1);
end;

# Build the ascending and descending normalizer-core chains starting from S <= G.
NormalizerCoreTower := function(G, S)
  local asc, cur, next, desc, coresAsc, coresDesc;
  asc := [S];
  cur := S;
  while cur <> G do
    next := Normalizer(G, cur);
    if next = cur then
      break;
    fi;
    Add(asc, next);
    cur := next;
  od;
  desc := Reversed(asc);
  coresAsc := List(asc, U -> Core(U, S));
  coresDesc := List([1..Length(desc)-1], k -> Core(desc[k], S));
  return rec(asc := asc, desc := desc, coresAsc := coresAsc, coresDesc := coresDesc);
end;

# Verify all normalizer, core, index, and two-point intersection conditions on the
# normalizer-core tower of S <= G for |G| = p^(2n-1).
VerifyExtremeTower := function(G, S, p)
  local m, n, tower;
  m := LogInt(Size(G), p);
  if m mod 2 = 0 then return false; fi;
  n := (m + 1) / 2;
  if Size(G) <> p^m or Size(S) <> p^(n - 1) or Size(Core(G, S)) <> 1 then
    return false;
  fi;
  tower := NormalizerCoreTower(G, S);
  if Length(tower.desc) <> n + 1 or tower.desc[1] <> G then
    return false;
  fi;
  return ForAll([1..n], k -> Index(tower.desc[k], tower.desc[k + 1]) = p)
     and ForAll([1..n], k -> Size(tower.coresDesc[k]) = p^(k - 1))
     and ForAll([1..n], k -> Normalizer(G, tower.coresDesc[k]) = tower.desc[k])
     and ForAll([1..n], k -> ForAll(RightTransversal(tower.desc[k], tower.desc[k + 1]),
           g -> g in tower.desc[k + 1] or Intersection(S, S^g) = tower.coresDesc[k]));
end;

# Compute the disjoint-layer fixed-point sum from a valid normalizer-core tower.
ExtremeLayerSieveF := function(G, tower)
  local n;
  n := Length(tower.desc) - 1;
  return 1 + Sum([1..n-1],
                 k -> Index(G, tower.desc[k + 1]) * (Size(tower.coresDesc[k + 1]) - Size(tower.coresDesc[k])));
end;

# Enumerate conjugacy-class representatives of core-free extreme stabilizers S <= G of order p^(n-1).
ExtremeStabilizerClasses := function(G, p)
  local N, m, n, target_f, res, c, S;
  N := Size(G);
  m := LogInt(N, p);
  if m mod 2 = 0 then return []; fi;
  n := (m + 1) / 2;
  target_f := ExtremeTargetF(p, m);
  res := [];
  for c in ConjugacyClassesSubgroups(G) do
    S := Representative(c);
    if Size(S) = p^(n - 1) and Size(Core(G, S)) = 1 and UltraFastF(G, S) = target_f then
      Add(res, S);
    fi;
  od;
  return res;
end;

# Fast extremality test on a p-group G of maximal class and odd order p^m (m >= 5 for p >= 5;
# full subgroup-class search for p = 3) via tilted stabilizers S = <x_4, x_2 * x_3^k>.
HasTiltedExtremeStabilizer := function(G, p)
  local m, n, target_f, x, k, S;
  if p = 3 then
    return Length(ExtremeStabilizerClasses(G, 3)) > 0;
  fi;
  m := LogInt(Size(G), p);
  if m mod 2 = 0 then return false; fi;
  n := (m + 1) / 2;
  target_f := ExtremeTargetF(p, m);
  x := Pcgs(G);
  for k in [0..p-1] do
    S := Subgroup(G, [x[4], x[2] * x[3]^k]);
    if Size(S) = p^(n - 1) and not (x[m] in S) and Size(Core(G, S)) = 1
       and UltraFastF(G, S) = target_f then
      return true;
    fi;
  od;
  return false;
end;

EXTREME_LIB_LOADED := true;
fi;
