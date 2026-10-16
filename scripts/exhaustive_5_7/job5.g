Read("lib/alpha_lib.g");
ClassCountF := function(G, S)
  local cls, s;
  cls := [];
  for s in AsList(S) do
    if not ForAny(cls, C -> s in C) then Add(cls, ConjugacyClass(G, s)); fi;
  od;
  return Sum(cls, Size);
end;
cons := ConsistentAlphas();
out := OutputTextFile("scripts/exhaustive_5_7/out5.txt", false);
SetPrintFormattingStatus(out, false);
for i in [1..Length(cons)] do
  if i mod 6 = 5 then
    a := cons[i];
    G := DescGroup(a); x := Pcgs(G);
    V := Subgroup(G, [x[6], x[7]]);
    hom := NaturalHomomorphismByNormalSubgroup(G, V); Q := Image(hom);
    extQ := Filtered(List(ConjugacyClassesSubgroups(Q), Representative),
              T -> Size(T) = 25 and Size(Core(Q,T)) = 1 and 6*ClassCountF(Q,T) = Size(Q)+1);
    fs := [];
    for P in List(extQ, T -> PreImage(hom, T)) do
      for H in MaximalSubgroups(P) do
        if Size(Intersection(H, V)) = 5 and Size(Core(G, H)) = 1 then
          Add(fs, ClassCountF(G, H));
        fi;
      od;
    od;
    S := Subgroup(G, [x[2], x[4]]);
    if Size(S) = 125 and Size(Core(G,S)) = 1 then f24 := ClassCountF(G, S); else f24 := -Size(S); fi;
    AppendTo(out, a, ";", Length(extQ), ";", Length(fs), ";", f24, ";", Collected(fs), ";",
             Maximum(Concatenation(fs,[0])), ";", NrConjugacyClasses(G), ";", Size(Centre(G)), "\n");
  fi;
od;
CloseStream(out);
QUIT;
