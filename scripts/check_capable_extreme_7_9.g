# check_capable_extreme_7_9.g
# Verify whether any of the 20 capable groups of order 7^9 below G(7, 5) are extreme
# (confirming that all 3,677 extreme groups of order 7^9 are terminal).
# Chain constructed via ANUPQ's CapableDescendants option, matching the mc-capable
# counts 9 / 29 / 20 / 0 at orders 7^7 .. 7^10 in branch_depth_extreme.g.

Read("lib/extreme_lib.g");
Read("lib/timings_lib.g");
RequirePackage("anupq");

RunCheckCapableExtreme79 := function()
  local Cap, G3, S4, c5, G75, g6, c7, ext7Count, c8, c9, ext9Count;
  Cap := G -> PqDescendants(G : StepSize := 1, CapableDescendants);
  G3 := ExtraspecialGroup(343, 7);
  S4 := Cap(G3)[1];
  c5 := Cap(S4);
  G75 := Filtered(c5, H -> not P1Abelian(H))[1];
  g6 := Cap(G75)[1];
  c7 := Cap(g6);
  ext7Count := Number(c7, H -> HasTiltedExtremeStabilizer(H, 7));
  Print("capable 7^7: ", Length(c7), ", extreme among them: ", ext7Count, "\n");
  c8 := Concatenation(List(c7, Cap));
  Print("capable 7^8: ", Length(c8), "\n");
  c9 := Concatenation(List(c8, Cap));
  ext9Count := Number(c9, H -> HasTiltedExtremeStabilizer(H, 7));
  Print("capable 7^9: ", Length(c9), ", extreme among them: ", ext9Count, "\n");
  if Length(c7) <> 9 or ext7Count <> 5 or Length(c8) <> 29 or Length(c9) <> 20 or ext9Count <> 0 then
    Error("Capable order-7^7..7^9 extreme count mismatch!");
  fi;
  PrintTimingIfEnabled();
end;

RunCheckCapableExtreme79();
QUIT;
