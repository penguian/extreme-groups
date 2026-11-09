# verify_fixed_point_layers.g
# For all 375 presentations with alpha_3 in {2, 3, 4}: S = <x_4, x_2 * x_3^{k_0}>,
# k_0 = (alpha_2 + alpha_6) / alpha_3 mod 5.
# Check the fixed-point distribution of the elements of S in the action on G / S:
#   1 element fixing 625, 4 fixing 125 (S_1 = <c>), 20 fixing 25 (S_2 \ S_1, S_2 = <x_4, c>),
#   100 fixing 5 (S \ S_2), and hence f = 13021.

Read("lib/alpha_lib.g");
Read("lib/timings_lib.g");

CheckFixedPointLayersOne := function(a)
  local G, x, k0, s1, S, c, S1, S2, act, N, fx, ok, f;
  G := DescGroup(a);
  x := AsList(Pcgs(G));
  k0 := ((a[2] + a[6]) * (1 / a[3] mod 5)) mod 5;
  s1 := x[2] * x[3]^k0;
  S := Subgroup(G, [x[4], s1]);
  c := Comm(x[4], s1);
  S1 := Subgroup(G, [c]);
  S2 := Subgroup(G, [x[4], c]);
  act := FactorCosetAction(G, S);
  N := 625;
  fx := s -> N - NrMovedPoints(Image(act, s));
  ok := Size(S) = 125 and Size(S2) = 25;
  ok := ok and ForAll(Elements(S), function(s)
          if s = One(G) then return fx(s) = 625;
          elif s in S1 then return fx(s) = 125;
          elif s in S2 then return fx(s) = 25;
          else return fx(s) = 5;
          fi;
        end);
  f := UltraFastF(G, S);
  return ok and f = 13021;
end;

RunVerifyFixedPointLayers := function()
  local alphas, bad;
  alphas := Filtered(ConsistentAlphas(), a -> a[3] in [2, 3, 4]);
  Print("presentations: ", Length(alphas), "\n");
  bad := Filtered(alphas, a -> not CheckFixedPointLayersOne(a));
  Print("failures: ", Length(bad), "\n");
  if Length(bad) > 0 then
    Error("Fixed-point layer verification failed on ", Length(bad), " presentations!");
  fi;
  Print("finished\n");
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t_script_start, " ms\n");
  fi;
end;

RunVerifyFixedPointLayers();
QUIT;
