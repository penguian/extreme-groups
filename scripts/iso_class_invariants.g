# iso_class_invariants.g
# Compute exponent, derived length, |Z(G)|, and derived series orders across all
# 70 isomorphism class representatives of order 5^7 from scripts/iso_classes.txt.

Read("lib/iso_orbits_lib.g");

RunIsoClassInvariants := function()
  local allreps, res, r, a, G, c;
  allreps := List(ReadIsoClasses57("scripts/iso_classes.txt"), r -> r.rep);

  res := [];
  for a in allreps do
    G := DescGroup(a);
    Add(res, [a[3] in [2, 3, 4], Exponent(G), DerivedLength(G), Size(Centre(G)),
              List(DerivedSeriesOfGroup(G), Size)]);
  od;
  Print("[extreme?, exponent, derived length, |Z|, derived series orders] -> #classes\n");
  for c in Collected(res) do
    Print(c, "\n");
  od;
end;

RunIsoClassInvariants();
QUIT;
