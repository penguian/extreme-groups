# check_capable_extreme_7_9.g
# Verify whether any of the 20 capable groups of order 7^9 below G(7, 5) are extreme
# (confirming that all 3,677 extreme groups of order 7^9 are terminal).
# Chain constructed via ANUPQ's CapableDescendants option, matching the mc-capable
# counts 9 / 29 / 20 / 0 at orders 7^7 .. 7^10 in branch_depth_extreme.g.

LoadPackage("anupq");
Read("lib/klg_lib.g");
Read("lib/timings_lib.g");

# Extremality test for a 7-group G of odd order 7^m (m = 2n - 1):
# check whether some core-free S = <x_4, x_2 * x_3^k> (k = 0..6) of order 7^(n-1)
# satisfies 8 * f(G, S) = 7^m + 1.
IsExtreme7 := function(G)
  local x, m, n, k, S;
  m := LogInt(Size(G), 7);
  n := (m + 1) / 2;
  x := Pcgs(G);
  for k in [0..6] do
    S := Subgroup(G, [x[4], x[2] * x[3]^k]);
    if Size(S) = 7^(n-1) and not (x[m] in S) and UltraFastF(G, S) = (7^m + 1) / 8 then
      return true;
    fi;
  od;
  return false;
end;

RunCheckCapableExtreme79 := function()
  local Cap, G3, S4, c5, G75, g6, c7, c8, c9;
  Cap := G -> PqDescendants(G : StepSize := 1, CapableDescendants);
  G3 := ExtraspecialGroup(343, 7);
  S4 := Cap(G3)[1];
  c5 := Cap(S4);
  G75 := Filtered(c5, H -> not P1Abelian(H))[1];
  g6 := Cap(G75)[1];
  c7 := Cap(g6);
  Print("capable 7^7: ", Length(c7), ", extreme among them: ", Number(c7, IsExtreme7), "\n");
  c8 := Concatenation(List(c7, Cap));
  Print("capable 7^8: ", Length(c8), "\n");
  c9 := Concatenation(List(c8, Cap));
  Print("capable 7^9: ", Length(c9), ", extreme among them: ", Number(c9, IsExtreme7), "\n");
  if SHOW_TIMINGS then
    Print("Total runtime: ", Runtime() - t_script_start, " ms\n");
  fi;
end;

RunCheckCapableExtreme79();
QUIT;
