# audit_paper_assertions.g
# Deterministic GAP 4.15.1 + ANUPQ 3.3.3 verification script auditing prose, side-remark,
# minimal faithful degree, table, and Appendix A dictionary assertions in
# "Revisiting extreme transitive p-groups of maximal class".
#
# Usage (from repository root):
#   gap -q scripts/audit_paper_assertions.g

LoadPackage("anupq");
Read("lib/timings_lib.g");
Read("lib/alpha_lib.g");
Read("lib/iso_orbits_lib.g");

t0_audit := Runtime();

Print("=== CHECK 1: Section 1 & Appendix A(2) Affine Chain-Ring Groups ===\n");
CheckAffineZpn := function(p, n)
  local deg, perms, u, G, S, f, orbs;
  deg := p^n;
  perms := [];
  Add(perms, PermList(List([0..deg-1], x -> ((x + 1) mod deg) + 1)));
  for u in [1..n-1] do
    Add(perms, PermList(List([0..deg-1], x -> (((1 + p^u) * x) mod deg) + 1)));
  od;
  G := Group(perms);
  S := Stabilizer(G, 1);
  f := Size(G) - Number(G, g -> NrMovedPoints(g) = deg);
  orbs := List(Orbits(S, [1..deg]), Length);
  Print("Z/", p, "^", n, "Z: |G|=", Size(G), " (exp ", p^(2*n-1), ")",
        " DL=", DerivedLength(G), " Class=", NilpotencyClassOfGroup(G),
        " |S|=", Size(S), " Core=", Size(Core(G, S)),
        " f=", f, " (p+1)f=|G|+1:", (p+1)*f = Size(G)+1,
        " Rank=", Length(orbs), " (exp ", n*(p-1)+1, ")\n");
  if Size(G) <> p^(2*n-1) or DerivedLength(G) <> 2 or NilpotencyClassOfGroup(G) <> n
     or (p+1)*f <> Size(G)+1 or Length(orbs) <> n*(p-1)+1 then
    Error("Mismatch in CheckAffineZpn!");
  fi;
end;

CheckAffineFpY := function(p, n)
  local deg, IntToPoly, PolyToInt, MulPoly, perms, i, u, G, S, f;
  deg := p^n;
  IntToPoly := function(x)
    local c, k;
    c := [];
    for k in [1..n] do
      Add(c, x mod p);
      x := QuoInt(x, p);
    od;
    return c;
  end;
  PolyToInt := function(c)
    local x, k;
    x := 0;
    for k in [n, n-1..1] do
      x := x * p + (c[k] mod p);
    od;
    return x;
  end;
  MulPoly := function(a, b)
    local c, i, j;
    c := List([1..n], k -> 0);
    for i in [1..n] do
      for j in [1..n+1-i] do
        c[i+j-1] := (c[i+j-1] + a[i]*b[j]) mod p;
      od;
    od;
    return c;
  end;
  perms := [];
  for i in [1..n] do
    u := List([1..n], k -> 0); u[i] := 1;
    Add(perms, PermList(List([0..deg-1], x -> PolyToInt(IntToPoly(x) + u) + 1)));
  od;
  for i in [1..n-1] do
    u := List([1..n], k -> 0); u[1] := 1; u[i+1] := 1;
    Add(perms, PermList(List([0..deg-1], x -> PolyToInt(MulPoly(IntToPoly(x), u)) + 1)));
  od;
  G := Group(perms);
  S := Stabilizer(G, 1);
  f := Size(G) - Number(G, g -> NrMovedPoints(g) = deg);
  Print("F_", p, "[y]/(y^", n, "): |G|=", Size(G),
        " DL=", DerivedLength(G), " Class=", NilpotencyClassOfGroup(G),
        " |S|=", Size(S), " Core=", Size(Core(G, S)),
        " f=", f, " (p+1)f=|G|+1:", (p+1)*f = Size(G)+1, "\n");
  if Size(G) <> p^(2*n-1) or DerivedLength(G) <> 2 or NilpotencyClassOfGroup(G) <> n
     or (p+1)*f <> Size(G)+1 then
    Error("Mismatch in CheckAffineFpY!");
  fi;
end;

for pair in [[3,2],[3,3],[3,4],[5,2],[5,3]] do
  CheckAffineZpn(pair[1], pair[2]);
  CheckAffineFpY(pair[1], pair[2]);
od;

Print("\n=== CHECK 2: Section 1, Section 2 mu(G), & Section 4 E_5 Lattice and Structure ===\n");
E5 := KLGpc(5, 5);
ccsE5 := ConjugacyClassesSubgroups(E5);
totSubsE5 := Sum(ccsE5, Size);
coreFreeE5 := Filtered(ccsE5, cl -> Size(Core(E5, Representative(cl))) = 1);
muE5 := Minimum(List(coreFreeE5, cl -> Index(E5, Representative(cl))));
extClassesE5 := Filtered(ccsE5, cl -> Size(Representative(cl)) = 25 and Size(Core(E5, Representative(cl))) = 1
                                      and 6 * UltraFastF(E5, Representative(cl)) = Size(E5) + 1);
Print("E_5 subgroup classes: ", Length(ccsE5), " (paper: 51); total subgroups: ", totSubsE5,
      " (paper: 1151); mu(E_5) = ", muE5, " (paper: 125)\n");
Print("E_5 extreme classes: ", Length(extClassesE5), " of size ", List(extClassesE5, Size),
      " (total ", Sum(extClassesE5, Size), ")\n");
if Length(ccsE5) <> 51 or totSubsE5 <> 1151 or muE5 <> 125
   or Length(extClassesE5) <> 5 or Sum(extClassesE5, Size) <> 125 then
  Error("E_5 lattice or mu(E_5) mismatch!");
fi;
F5 := FreeGroup(5); f5 := GeneratorsOfGroup(F5);
c5 := SingleCollector(F5, [5,5,5,5,5]);
SetCommutator(c5, 2, 1, f5[3]); SetCommutator(c5, 3, 1, f5[4]);
SetCommutator(c5, 4, 1, f5[5]); SetCommutator(c5, 3, 2, f5[5]);
UpdatePolycyclicCollector(c5);
E5pres := GroupByRwsNC(c5);
xp := Pcgs(E5pres);
E1 := Subgroup(E5pres, [xp[2], xp[3], xp[4], xp[5]]);
Heis5 := ExtraspecialGroup(125, 5);
Print("E5pres =~ KLGpc(5,5): ", IsomorphismGroups(E5pres, E5) <> fail,
      "; E_1 =~ Heis_5 x C_5: ", IdGroup(E1) = IdGroup(DirectProduct(Heis5, CyclicGroup(5))), "\n");
Tlist := List([0..4], k -> Subgroup(E5pres, [xp[4], xp[2]*xp[3]^k]));
autE5 := AutomorphismGroup(E5pres);
orbT0 := Orbit(autE5, Tlist[1], function(H, phi) return Image(phi, H); end);
matchedTk := Filtered(Tlist, T -> ForAny(orbT0, U -> IsConjugate(E5pres, T, U)));
Print("All 5 T_k pairwise non-conjugate: ",
      ForAll([1..5], i -> ForAll([i+1..5], j -> not IsConjugate(E5pres, Tlist[i], Tlist[j]))),
      "; single Aut(E_5)-orbit: ", Length(matchedTk) = 5,
      "; N_{E_5}(T_0) = <x_2,x_4,x_5>: ",
      Normalizer(E5pres, Tlist[1]) = Subgroup(E5pres, [xp[2], xp[4], xp[5]]), "\n");

Print("\n=== CHECK 3: Section 3 Literal 1982 NICE Clause (2) Counterexample for k >= j+2 ===\n");
Gext := DescGroup([0,1,2,4,0,0]);
xG := Pcgs(Gext);
Sext := Subgroup(Gext, [xG[4], xG[2]*xG[3]^3]);
H2_true := Subgroup(Gext, [xG[4], Comm(xG[4], xG[2]*xG[3]^3)]);
conjsH2 := Orbit(Gext, H2_true);
interSizes := Collected(List(Filtered(Cartesian(conjsH2, conjsH2), p -> p[1] <> p[2]),
                             p -> Size(Intersection(p[1], p[2]))));
Print("H_2 conjugates count: ", Length(conjsH2), " (25); pairwise distinct intersection sizes: ", interSizes, "\n");
if Length(conjsH2) <> 25 or interSizes <> [ [ 1, 500 ], [ 5, 100 ] ] then
  Error("Literal NICE Clause (2) check mismatch!");
fi;

Print("\n=== CHECK 4: Section 5 Cases 2 & 3, Table 1 |Aut G|, and Section 7.2 Nine Tuples ===\n");
Gcase2 := DescGroup([0,4,0,1,0,1]);
xc2 := Pcgs(Gcase2); Sc2 := Subgroup(Gcase2, [xc2[2], xc2[4]]);
Print("Case 2: |S_0|=", Size(Sc2), " |N_G(S_0)|=", Size(Normalizer(Gcase2, Sc2)),
      " f=", UltraFastF(Gcase2, Sc2), " (paper: 3021)\n");
Gcase3 := DescGroup([0,0,1,0,0,0]);
xc3 := Pcgs(Gcase3); Sc3 := Subgroup(Gcase3, [xc3[2], xc3[4]]);
interC3 := Intersection(Sc3, Sc3^xc3[5]);
Print("Case 3: |S_0|=", Size(Sc3), " S cap S^(x_5) = <x_4,x_6>: ",
      interC3 = Subgroup(Gcase3, [xc3[4], xc3[6]]),
      " [G : N(S cap S^x5)]=", Index(Gcase3, Normalizer(Gcase3, interC3)),
      " f=", UltraFastF(Gcase3, Sc3), " (paper: 12621, deficit=", 13021 - UltraFastF(Gcase3, Sc3), ")\n");
if UltraFastF(Gcase2, Sc2) <> 3021 or UltraFastF(Gcase3, Sc3) <> 12621 then
  Error("Case 2 or Case 3 fixed-point count mismatch!");
fi;

lines := InputTextFile("scripts/iso_classes.txt");
isoRecs := [];
while not IsEndOfStream(lines) do
  l := ReadLine(lines);
  if l <> fail then
    s := SplitString(Chomp(l), ";");
    Add(isoRecs, rec(idx := EvalString(s[1]), rep := EvalString(s[2]),
                     aut := EvalString(s[5]), orb := EvalString(s[6])));
  fi;
od;
CloseStream(lines);
Print("Loaded iso_classes.txt records: ", Length(isoRecs), "\n");

for a3 in [0..4] do
  sub := Filtered(isoRecs, r -> r.rep[3] = a3);
  autSizes := Collected(List(sub, r -> r.aut));
  ccCounts := Set(List(sub, r -> NrConjugacyClasses(DescGroup(r.rep))));
  dlSet := Set(List(sub, r -> DerivedLength(DescGroup(r.rep))));
  expSet := Set(List(sub, r -> Exponent(DescGroup(r.rep))));
  zSet := Set(List(sub, r -> Size(Centre(DescGroup(r.rep)))));
  Print("alpha_3=", a3, ": #classes=", Length(sub), " DL=", dlSet, " Exp=", expSet,
        " |Z|=", zSet, " #cc=", ccCounts, " |Aut|=", autSizes, "\n");
od;
for a3 in [0..4] do
  r := First(isoRecs, x -> x.rep[3] = a3);
  if Size(AutomorphismGroup(DescGroup(r.rep))) <> r.aut then
    Error("AutomorphismGroup mismatch on ", r.rep);
  fi;
od;
Print("Direct AutomorphismGroup cross-check on 5 sector reps: PASS\n");

nine := [
  [0,1,2,4,0,0], [0,1,2,4,2,0], [0,1,2,4,3,0],
  [0,2,3,3,0,2], [0,2,3,3,1,2], [0,2,3,3,2,2],
  [0,3,4,2,0,4], [0,3,4,2,1,4], [0,3,4,2,2,4]
];
nineOrbIdx := [];
for t in nine do
  if not IsConfluent(DescColl(t)) then Error("Tuple not confluent: ", t); fi;
  k0 := ((t[2] + t[6]) * (t[3]^3)) mod 5;
  r := First(isoRecs, x -> t in x.orb);
  hasTypeIV := ForAny(r.orb, u -> ((u[2] + u[6]) mod 5) = 0);
  if k0 <> 3 or hasTypeIV then Error("Nine-tuple check failed on ", t); fi;
  Add(nineOrbIdx, r.idx);
od;
Print("Section 7.2 nine tuples: all confluent, all k_0=3, all Type-I-only, distinct classes=",
      Length(Set(nineOrbIdx)), " (expected 9)\n");

Print("\n=== CHECK 5: Section 8.3 Sector mu_3 = 6*lambda (d7[85]) 409 Non-Extreme Descendants at 7^9 ===\n");
G73 := ExtraspecialGroup(7^3, 7);
d74 := Filtered(PqDescendants(G73 : StepSize := 1, CapableDescendants), g -> NilpotencyClassOfGroup(g) = 3);
d75 := Filtered(PqDescendants(d74[1] : StepSize := 1, CapableDescendants),
                g -> NilpotencyClassOfGroup(g) = 4 and not P1Abelian(g));
d76 := Filtered(PqDescendants(d75[1] : StepSize := 1, CapableDescendants), g -> NilpotencyClassOfGroup(g) = 5);
d77 := PqDescendants(d76[1] : StepSize := 1);
g85 := d77[85];
x85 := Pcgs(g85);
mu3_85 := ExponentsOfPcElement(x85, Comm(x85[4], x85[3]))[7];
cap8_85 := PqDescendants(g85 : StepSize := 1, CapableDescendants);
d9_85 := Concatenation(List(cap8_85, h -> PqDescendants(h : StepSize := 1)));
allP1P6Triv := ForAll(d9_85, function(G)
  local L, P1g;
  L := LowerCentralSeriesOfGroup(G);
  P1g := TwoStepCentralizer(G);
  return IsTrivial(CommutatorSubgroup(P1g, L[6]));
end);
Print("d7[85]: mu_3=", mu3_85, " |cap8|=", Length(cap8_85),
      " |d9|=", Length(d9_85), " (paper: 409); all [P_1,P_6]=1: ", allP1P6Triv, "\n");
if mu3_85 <> 6 or Length(d9_85) <> 409 or not allP1P6Triv then
  Error("d7[85] 409 check failed!");
fi;

Print("\n=== CHECK 6: Appendix A(2) GAP SimpleLieAlgebra(\"W\", [1], GF(p)) Divided-Power Basis ===\n");
CheckWittDividedPowerBasis := function(p)
  local W, b, u, okPlus, i, j;
  W := SimpleLieAlgebra("W", [1], GF(p));
  b := CanonicalBasis(W);
  u := List([1..p-2], i -> (-Factorial(i+1) * One(GF(p))) * b[i+2]);
  okPlus := true;
  for i in [1..p-2] do
    for j in [1..p-2] do
      if i + j <= p - 2 then
        if u[i] * u[j] <> ((i - j) * One(GF(p))) * u[i+j] then okPlus := false; fi;
      fi;
    od;
  od;
  Print("p=", p, ": dim(W)=", Length(b),
        ", u_i = -(i+1)! b_{i+2} satisfies [u_i,u_j] = (i-j)u_{i+j} for i+j<=", p-2, ": ", okPlus, "\n");
  if not okPlus then Error("Witt divided-power basis check failed!"); fi;
end;

for p in [7, 11] do
  CheckWittDividedPowerBasis(p);
od;

if SHOW_TIMINGS then
  Print("Total runtime: ", Runtime() - t0_audit, " ms\n");
fi;

QUIT;
