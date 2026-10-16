# Exact isomorphism orbits within the 1982 descendant pcp family (no anupq / SmallGroups needed).
#
# Method. Let G = G_alpha. G1 := C_G(gamma2/gamma4) is characteristic of index 5, and the family
# pcp has x1 notin G1, x2 in G1 \ gamma2 (both checked below). An isomorphism G_beta -> G_alpha
# sends (x1,x2) to a pair (y1,y2) with y1 notin G1, y2 in G1 \ gamma2, and, up to an inner
# automorphism of G_alpha, y1 is one of the conjugacy-class representatives. Conversely, if
# (y1,y2) satisfies every relation of the beta-pcp (with y3..y7 the iterated commutators), then
# there is an epimorphism G_beta -> <y1,y2> = G_alpha, an isomorphism since both have order 5^7.
# So Orbit(alpha) = { beta read off from fitting pairs (r, y2) }, exactly.
# Also |Aut(G_alpha)| = sum over reps r of |r^G| * #{ y2 : (r,y2) fits with beta = alpha }.
Read("lib/alpha_lib.g");

# Exponent e with z = x7^e, or fail if z notin <x7>.
Z7 := function(pcgs, z)
  local e;
  e := ExponentsOfPcElement(pcgs, z);
  if ForAny([1..6], i -> e[i] <> 0) then return fail; fi;
  return e[7];
end;

# Return beta (list of 6 residues) if (y1,y2) fits the family pcp, else fail.
FitPair := function(pcgs, y1, y2)
  local y3, y4, y5, y6, y7, c, inv, b, t, one, e;
  one := One(y1);
  y3 := Comm(y2, y1); y4 := Comm(y3, y1); y5 := Comm(y4, y1);
  y6 := Comm(y5, y1); y7 := Comm(y6, y1);
  if y7 = one then return fail; fi;
  c := Z7(pcgs, y7);
  if c = fail or c = 0 then return fail; fi;
  inv := Inverse(c) mod 5;
  b := [];
  # [y3,y2] = y5 y7^b1 ; [y4,y2] = y6 y7^b2 ; [y5,y2] = y7^b3 ; [y4,y3] = y7^b4
  t := Z7(pcgs, y5^-1 * Comm(y3, y2)); if t = fail then return fail; fi; b[1] := t*inv mod 5;
  t := Z7(pcgs, y6^-1 * Comm(y4, y2)); if t = fail then return fail; fi; b[2] := t*inv mod 5;
  t := Z7(pcgs, Comm(y5, y2));         if t = fail then return fail; fi; b[3] := t*inv mod 5;
  t := Z7(pcgs, Comm(y4, y3));         if t = fail then return fail; fi; b[4] := t*inv mod 5;
  # y1^5 = y7^b5 ; y2^5 = y6^4 y7^b6 ; y3^5 = y7^4
  t := Z7(pcgs, y1^5);                 if t = fail then return fail; fi; b[5] := t*inv mod 5;
  t := Z7(pcgs, y6^-4 * y2^5);         if t = fail then return fail; fi; b[6] := t*inv mod 5;
  if y3^5 <> y7^4 then return fail; fi;
  # remaining relations of the pcp are trivial
  if y4^5 <> one or y5^5 <> one or y6^5 <> one or y7^5 <> one then return fail; fi;
  if Comm(y6, y2) <> one or Comm(y7, y2) <> one then return fail; fi;
  if Comm(y5, y3) <> one or Comm(y6, y3) <> one or Comm(y7, y3) <> one then return fail; fi;
  if Comm(y5, y4) <> one or Comm(y6, y4) <> one or Comm(y7, y4) <> one then return fail; fi;
  if Comm(y6, y5) <> one or Comm(y7, y5) <> one or Comm(y7, y6) <> one then return fail; fi;
  return b;
end;

# Orbit of alpha within the family, and |Aut(G_alpha)|.
OrbitAndAut := function(a)
  local G, pcgs, x, L, G1, g2, reps, y2s, orb, aut, r, y2, b, cnt, cs;
  G := DescGroup(a);
  pcgs := Pcgs(G); x := pcgs;
  L := LowerCentralSeriesOfGroup(G);
  # C_G(gamma2/gamma4): elements g with [gamma2, g] <= gamma4
  G1 := Filtered(MaximalSubgroups(G), M -> ForAll(GeneratorsOfGroup(L[2]),
            h -> ForAll(GeneratorsOfGroup(M), g -> Comm(h, g) in L[4])));
  if Length(G1) <> 1 then Error("G1 not unique for ", a); fi;
  G1 := G1[1];
  if x[1] in G1 or not x[2] in G1 then Error("x1/x2 not positioned as expected for ", a); fi;
  g2 := L[2];
  cs := Filtered(ConjugacyClasses(G), C -> not Representative(C) in G1);
  y2s := Filtered(AsList(G1), g -> not g in g2);
  orb := []; aut := 0;
  for r in cs do
    cnt := 0;
    for y2 in y2s do
      b := FitPair(pcgs, Representative(r), y2);
      if b <> fail then
        AddSet(orb, b);
        if b = a then cnt := cnt + 1; fi;
      fi;
    od;
    aut := aut + Size(r) * cnt;
  od;
  return rec(alpha := a, orbit := orb, aut := aut);
end;
