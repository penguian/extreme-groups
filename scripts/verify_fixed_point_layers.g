# verify_fixed_point_layers.g  (11 Oct 2026)
# For all 375 presentations with alpha3 in {2,3,4}: S = <x4, x2*x3^k0>, k0 = (a2+a6)/a3 mod 5.
# Check the fixed-point distribution of the elements of S in the action on G/S:
#   1 element fixing 625, 4 fixing 125 (S1 = <c>), 20 fixing 25 (S2 \ S1, S2 = <x4,c>), 100 fixing 5 (S \ S2),
# and hence f = 13021.
Read("lib/alpha_lib.g");
alphas := Filtered(ConsistentAlphas(), a -> a[3] in [2,3,4]);
Print("presentations: ", Length(alphas), "\n");
CheckOne := function(a)
  local G, x, k0, s1, S, c, S1, S2, act, N, fx, ok, f;
  G := DescGroup(a); x := AsList(Pcgs(G));
  k0 := ((a[2] + a[6]) * (1/a[3] mod 5)) mod 5;
  s1 := x[2]*x[3]^k0; S := Subgroup(G, [x[4], s1]);
  c := Comm(x[4], s1); S1 := Subgroup(G, [c]); S2 := Subgroup(G, [x[4], c]);
  act := FactorCosetAction(G, S); N := 625;
  fx := s -> N - NrMovedPoints(Image(act, s));
  ok := Size(S) = 125 and Size(S2) = 25;
  ok := ok and ForAll(Elements(S), function(s)
          if s = One(G) then return fx(s) = 625;
          elif s in S1 then return fx(s) = 125;
          elif s in S2 then return fx(s) = 25;
          else return fx(s) = 5; fi; end);
  f := Sum(Filtered(ConjugacyClasses(Image(act)), cl -> NrMovedPoints(Representative(cl)) < N), Size);
  return ok and f = 13021;
end;
bad := Filtered(alphas, a -> not CheckOne(a));
Print("failures: ", Length(bad), "\n");
Print("finished\n");
QUIT;
