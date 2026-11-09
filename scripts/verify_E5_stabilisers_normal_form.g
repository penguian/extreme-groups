# verify_E5_stabilisers_normal_form.g
# Cross-check of Lemma 4.2: in E_5 = G / V, every subgroup
#   T(k, j, b) = < x_2 * x_3^k * x_5^b, x_4 * x_5^j >   (k, j, b in F_5)
# has order 25, is core-free, has f = 521, lies in E_1 = <x_2..x_5>, and is conjugate to T_{k-j}.

Read("lib/alpha_lib.g");
Read("lib/timings_lib.g");

RunVerifyE5Stabilisers := function()
  local alphas, a, G, x, V, hom, E5q, y, E1, bad, cnt, k, j, b, T, Tk;
  alphas := ConsistentAlphas();
  a := alphas[1];
  G := DescGroup(a);
  x := AsList(Pcgs(G));
  V := Subgroup(G, x{[6, 7]});
  hom := NaturalHomomorphismByNormalSubgroup(G, V);
  E5q := Image(hom);
  y := List([1..5], i -> Image(hom, x[i]));
  E1 := Subgroup(E5q, y{[2..5]});
  bad := 0;
  cnt := 0;
  for k in [0..4] do
    for j in [0..4] do
      for b in [0..4] do
        T := Subgroup(E5q, [y[2] * y[3]^k * y[5]^b, y[4] * y[5]^j]);
        Tk := Subgroup(E5q, [y[4], y[2] * y[3]^((k - j) mod 5)]);
        cnt := cnt + 1;
        if not (Size(T) = 25 and Size(Core(E5q, T)) = 1 and UltraFastF(E5q, T) = 521
                and IsSubgroup(E1, T) and IsConjugate(E5q, T, Tk)) then
          bad := bad + 1;
        fi;
      od;
    od;
  od;
  Print("T(k,j,b) tested: ", cnt, "; failures: ", bad, "\n");
  Print("|E5| = ", Size(E5q), ", exponent 5: ", Exponent(E5q) = 5, "\n");
  if bad > 0 or Size(E5q) <> 3125 or Exponent(E5q) <> 5 then
    Error("E5 stabilisers normal form verification failed!");
  fi;
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t_script_start, " ms\n");
  fi;
end;

RunVerifyE5Stabilisers();
QUIT;
