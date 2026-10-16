Read("lib/alpha_lib.g");
reps := [[0,1,2,4,0,0], [0,1,2,4,0,4], [0,0,1,0,0,0], [0,0,1,0,0,1], [2,0,1,0,1,3]];
lines := InputTextFile("scripts/iso_classes.txt");
allreps := [];
while not IsEndOfStream(lines) do
  l := ReadLine(lines);
  if l <> fail then
    s := SplitString(Chomp(l), ";");
    Add(allreps, EvalString(s[2]));
  fi;
od;
res := [];
for a in allreps do
  G := DescGroup(a);
  Add(res, [a[3] in [2,3,4], Exponent(G), DerivedLength(G), Size(Centre(G)),
            List(DerivedSeriesOfGroup(G), Size)]);
od;
Print("[extreme?, exponent, derived length, |Z|, derived series orders] -> #classes\n");
for c in Collected(res) do Print(c, "\n"); od;
QUIT;
