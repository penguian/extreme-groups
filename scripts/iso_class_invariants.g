# iso_class_invariants.g
# Compute exponent, derived length, |Z(G)|, and derived series orders across all
# 70 isomorphism class representatives of order 5^7 from scripts/iso_classes.txt.

Read("lib/alpha_lib.g");

RunIsoClassInvariants := function()
  local lines, allreps, l, s, res, a, G, c;
  lines := InputTextFile("scripts/iso_classes.txt");
  allreps := [];
  while not IsEndOfStream(lines) do
    l := ReadLine(lines);
    if l <> fail then
      s := SplitString(Chomp(l), ";");
      Add(allreps, EvalString(s[2]));
    fi;
  od;
  CloseStream(lines);

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
