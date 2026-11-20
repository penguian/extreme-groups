# verify_auxiliary_assertions.g
# Deterministic GAP + ANUPQ verification script checking structural examples,
# subgroup lattice counts, minimal faithful degrees, non-extreme presentation types,
# Type-I-only tuples, sector mu_3 = 6*lambda (d7[85]), and modular Witt basis rescaling.
#
# Usage (from repository root):
#   gap -q scripts/verify_auxiliary_assertions.g

Read("lib/iso_orbits_lib.g");
Read("lib/timings_lib.g");
RequirePackage("anupq");

# Check 1(a): Affine extreme group x |-> a*x + b over Z/p^n Z (a === 1 mod p).
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
     or Size(S) <> p^(n-1) or Size(Core(G, S)) <> 1
     or (p+1)*f <> Size(G)+1 or Length(orbs) <> n*(p-1)+1 then
    Error("Mismatch in CheckAffineZpn!");
  fi;
end;

# Check 1(b): Affine extreme group over F_p[y]/(y^n) via base-p bijection with {1..p^n}.
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
     or Size(S) <> p^(n-1) or Size(Core(G, S)) <> 1
     or (p+1)*f <> Size(G)+1 then
    Error("Mismatch in CheckAffineFpY!");
  fi;
end;

# Check 2: E_5 subgroup lattice, minimal faithful degree mu(E_5), and stabilizer orbit structure.
CheckE5LatticeAndStructure := function()
  local E5, ccsE5, totSubsE5, coreFreeE5, muE5, extClassesE5,
        F5, f5, c5, E5pres, xp, E1, Heis5, isoE5ok, idE1ok,
        Tlist, autE5, orbT0, matchedTk, nonConjTk, singleOrbTk, normT0ok;
  E5 := KLGpc(5, 5);
  ccsE5 := ConjugacyClassesSubgroups(E5);
  totSubsE5 := Sum(ccsE5, Size);
  coreFreeE5 := Filtered(ccsE5, cl -> Size(Core(E5, Representative(cl))) = 1);
  muE5 := Minimum(List(coreFreeE5, cl -> Index(E5, Representative(cl))));
  extClassesE5 := Filtered(ccsE5, cl -> Size(Representative(cl)) = 25 and Size(Core(E5, Representative(cl))) = 1
                                        and 6 * UltraFastF(E5, Representative(cl)) = Size(E5) + 1);
  Print("E_5 subgroup classes: ", Length(ccsE5), " (expected: 51); total subgroups: ", totSubsE5,
        " (expected: 1151); mu(E_5) = ", muE5, " (expected: 125)\n");
  Print("E_5 extreme classes: ", Length(extClassesE5), " of size ", List(extClassesE5, Size),
        " (total ", Sum(extClassesE5, Size), ")\n");
  if Length(ccsE5) <> 51 or totSubsE5 <> 1151 or muE5 <> 125
     or Length(extClassesE5) <> 5 or List(extClassesE5, Size) <> [ 25, 25, 25, 25, 25 ]
     or Sum(extClassesE5, Size) <> 125 then
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
  isoE5ok := IsomorphismGroups(E5pres, E5) <> fail;
  idE1ok := IdGroup(E1) = IdGroup(DirectProduct(Heis5, CyclicGroup(5)));
  Print("E5pres =~ KLGpc(5,5): ", isoE5ok,
        "; E_1 =~ Heis_5 x C_5: ", idE1ok, "\n");
  Tlist := List([0..4], k -> Subgroup(E5pres, [xp[4], xp[2]*xp[3]^k]));
  autE5 := AutomorphismGroup(E5pres);
  orbT0 := Orbit(autE5, Tlist[1], function(H, phi) return Image(phi, H); end);
  matchedTk := Filtered(Tlist, T -> ForAny(orbT0, U -> IsConjugate(E5pres, T, U)));
  nonConjTk := ForAll([1..5], i -> ForAll([i+1..5], j -> not IsConjugate(E5pres, Tlist[i], Tlist[j])));
  singleOrbTk := Length(matchedTk) = 5;
  normT0ok := Normalizer(E5pres, Tlist[1]) = Subgroup(E5pres, [xp[2], xp[4], xp[5]]);
  Print("All 5 T_k pairwise non-conjugate: ", nonConjTk,
        "; single Aut(E_5)-orbit: ", singleOrbTk,
        "; N_{E_5}(T_0) = <x_2,x_4,x_5>: ", normT0ok, "\n");
  if not (isoE5ok and idE1ok and nonConjTk and singleOrbTk and normT0ok) then
    Error("E_5 structural presentation, stabilizer orbit, or normalizer check failed!");
  fi;
end;

# Check 3: Distinct conjugates of H_2 in an extreme order-5^7 group do not intersect strictly in H_1:
# pairs of elements from distinct G_3-blocks can intersect in 1 rather than H_1 (order 5).
CheckNonAdjacentConjugateIntersectionsH2 := function()
  local Gext, xG, H2_true, conjsH2, interSizes;
  Gext := DescGroup([0,1,2,4,0,0]);
  xG := Pcgs(Gext);
  H2_true := Subgroup(Gext, [xG[4], Comm(xG[4], xG[2]*xG[3]^3)]);
  conjsH2 := Orbit(Gext, H2_true);
  interSizes := Collected(List(Filtered(Cartesian(conjsH2, conjsH2), p -> p[1] <> p[2]),
                               p -> Size(Intersection(p[1], p[2]))));
  Print("H_2 conjugates count: ", Length(conjsH2), " (25); pairwise distinct intersection sizes: ", interSizes, "\n");
  if Length(conjsH2) <> 25 or interSizes <> [ [ 1, 500 ], [ 5, 100 ] ] then
    Error("Non-adjacent conjugate intersection check for H_2 failed!");
  fi;
end;

# Check 4: Order-5^7 non-extreme Type II & III examples, class invariants & |Aut G|, and 9 Type-I-only tuples.
CheckOrder57NonExtremeTypesAndTable := function()
  local Gtype2, xc2, Sc2, normT2, fType2,
        Gtype3, xc3, Sc3, interT3, interT3ok, idxNormT3, fType3,
        isoRecs, a3, sub, autSizes, ccCounts, dlSet, expSet, zSet, expCC, r,
        nine, nineOrbIdx, t, k0, hasTypeIV;

  Gtype2 := DescGroup([0,4,0,1,0,1]);
  xc2 := Pcgs(Gtype2); Sc2 := Subgroup(Gtype2, [xc2[2], xc2[4]]);
  normT2 := Size(Normalizer(Gtype2, Sc2));
  fType2 := UltraFastF(Gtype2, Sc2);
  Print("Type II: |S_0|=", Size(Sc2), " |N_G(S_0)|=", normT2,
        " f=", fType2, " (expected: 3021)\n");

  Gtype3 := DescGroup([0,0,1,0,0,0]);
  xc3 := Pcgs(Gtype3); Sc3 := Subgroup(Gtype3, [xc3[2], xc3[4]]);
  interT3 := Intersection(Sc3, Sc3^xc3[5]);
  interT3ok := interT3 = Subgroup(Gtype3, [xc3[4], xc3[6]]);
  idxNormT3 := Index(Gtype3, Normalizer(Gtype3, interT3));
  fType3 := UltraFastF(Gtype3, Sc3);
  Print("Type III: |S_0|=", Size(Sc3), " S cap S^(x_5) = <x_4,x_6>: ", interT3ok,
        " [G : N(S cap S^x5)]=", idxNormT3,
        " f=", fType3, " (expected: 12621, deficit=", 13021 - fType3, ")\n");
  if Size(Sc2) <> 125 or normT2 <> 3125 or fType2 <> 3021
     or Size(Sc3) <> 125 or not interT3ok or idxNormT3 <> 5 or fType3 <> 12621 then
    Error("Type II or Type III structural or fixed-point count mismatch!");
  fi;

  isoRecs := ReadIsoClasses57("scripts/iso_classes.txt");
  Print("Loaded iso_classes.txt records: ", Length(isoRecs), "\n");
  if Length(isoRecs) <> 70 then
    Error("Expected 70 isomorphism class records in scripts/iso_classes.txt!");
  fi;

  for a3 in [0..4] do
    sub := Filtered(isoRecs, r -> r.rep[3] = a3);
    autSizes := Collected(List(sub, r -> r.aut));
    ccCounts := Set(List(sub, r -> NrConjugacyClasses(DescGroup(r.rep))));
    dlSet := Set(List(sub, r -> DerivedLength(DescGroup(r.rep))));
    expSet := Set(List(sub, r -> Exponent(DescGroup(r.rep))));
    zSet := Set(List(sub, r -> Size(Centre(DescGroup(r.rep)))));
    Print("alpha_3=", a3, ": #classes=", Length(sub), " DL=", dlSet, " Exp=", expSet,
          " |Z|=", zSet, " #cc=", ccCounts, " |Aut|=", autSizes, "\n");
    if a3 = 1 then
      if Length(sub) <> 38 or dlSet <> [ 2 ] or expSet <> [ 25 ] or zSet <> [ 5 ]
         or ccCounts <> [ 173 ]
         or autSizes <> [ [ 9765625, 25 ], [ 19531250, 12 ], [ 39062500, 1 ] ] then
        Error("Order-5^7 class invariant mismatch at alpha_3 = 1!");
      fi;
    else
      if a3 = 0 then expCC := [ 173 ]; else expCC := [ 77 ]; fi;
      if Length(sub) <> 8 or dlSet <> [ 3 ] or expSet <> [ 25 ] or zSet <> [ 5 ]
         or ccCounts <> expCC
         or autSizes <> [ [ 1953125, 5 ], [ 3906250, 2 ], [ 7812500, 1 ] ] then
        Error("Order-5^7 class invariant mismatch at alpha_3 = ", a3);
      fi;
    fi;
  od;
  for a3 in [0..4] do
    r := First(isoRecs, x -> x.rep[3] = a3);
    if r = fail or Size(AutomorphismGroup(DescGroup(r.rep))) <> r.aut then
      Error("AutomorphismGroup mismatch on a3=", a3);
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
    r := First(isoRecs, x -> t in x.orbit);
    if r = fail then Error("Tuple not found in iso_classes.txt orbits: ", t); fi;
    hasTypeIV := ForAny(r.orbit, u -> ((u[2] + u[6]) mod 5) = 0);
    if k0 <> 3 or hasTypeIV then Error("Nine-tuple check failed on ", t); fi;
    Add(nineOrbIdx, r.idx);
  od;
  Print("Nine Type-I-only tuples: all confluent, all k_0=3, all Type-I-only, distinct classes=",
        Length(Set(nineOrbIdx)), " (expected 9)\n");
  if Length(Set(nineOrbIdx)) <> 9 then
    Error("Nine Type-I-only tuples did not map to 9 distinct isomorphism classes!");
  fi;
end;

# Check 5: Order-7^9 sector mu_3 = 6*lambda (d7[85]): 409 non-extreme descendants with [P_1, P_6] = 1.
CheckOrder79SectorMu3Eq6 := function()
  local G73, d74, d75, d76, d77, g85, x85, mu3_85, cap8_85, d9_85, allP1P6Triv;
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
        " |d9|=", Length(d9_85), " (expected: 409); all [P_1,P_6]=1: ", allP1P6Triv, "\n");
  if mu3_85 <> 6 or Length(cap8_85) <> 2 or Length(d9_85) <> 409 or not allP1P6Triv then
    Error("d7[85] 409 check failed!");
  fi;
end;

# Check 6: GAP SimpleLieAlgebra("W", [1], GF(p)) divided-power basis rescaling to positive Witt brackets.
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
  if Length(b) <> p or not okPlus then
    Error("Witt divided-power basis check failed!");
  fi;
end;

RunVerifyAuxiliaryAssertions := function()
  local pair, p;
  Print("=== CHECK 1: Affine Chain-Ring Extreme Groups ===\n");
  for pair in [[3,2],[3,3],[3,4],[5,2],[5,3]] do
    CheckAffineZpn(pair[1], pair[2]);
    CheckAffineFpY(pair[1], pair[2]);
  od;

  Print("\n=== CHECK 2: Base Group E_5 Lattice, mu(E_5), and Stabilizer Orbits ===\n");
  CheckE5LatticeAndStructure();

  Print("\n=== CHECK 3: Non-Adjacent Conjugate Intersections for H_2 at Order 5^7 ===\n");
  CheckNonAdjacentConjugateIntersectionsH2();

  Print("\n=== CHECK 4: Order-5^7 Non-Extreme Types II/III, Class Invariants, and Nine Type-I-Only Tuples ===\n");
  CheckOrder57NonExtremeTypesAndTable();

  Print("\n=== CHECK 5: Order-7^9 Sector mu_3 = 6*lambda (d7[85]) 409 Non-Extreme Descendants ===\n");
  CheckOrder79SectorMu3Eq6();

  Print("\n=== CHECK 6: GAP SimpleLieAlgebra(\"W\", [1], GF(p)) Divided-Power Witt Basis ===\n");
  for p in [7, 11] do
    CheckWittDividedPowerBasis(p);
  od;

  PrintTimingIfEnabled();
end;

RunVerifyAuxiliaryAssertions();
QUIT;
