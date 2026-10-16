# Library: the 1982 descendant pcp as a pc group, for alpha in (Z/5)^6 (consistent ones only).
DescColl := function(a)
  local F, x, c;
  F := FreeGroup(7); x := GeneratorsOfGroup(F);
  c := SingleCollector(F, [5,5,5,5,5,5,5]);
  SetPower(c, 1, x[7]^a[5]);
  SetPower(c, 2, x[6]^4*x[7]^a[6]);
  SetPower(c, 3, x[7]^4);
  SetCommutator(c, 2, 1, x[3]);
  SetCommutator(c, 3, 1, x[4]);
  SetCommutator(c, 4, 1, x[5]);
  SetCommutator(c, 5, 1, x[6]);
  SetCommutator(c, 6, 1, x[7]);
  SetCommutator(c, 3, 2, x[5]*x[7]^a[1]);
  SetCommutator(c, 4, 2, x[6]*x[7]^a[2]);
  SetCommutator(c, 5, 2, x[7]^a[3]);
  SetCommutator(c, 4, 3, x[7]^a[4]);
  UpdatePolycyclicCollector(c);
  return c;
end;
DescGroup := function(a)
  local c;
  c := DescColl(a);
  if not IsConfluent(c) then Error("inconsistent alpha ", a); fi;
  return GroupByRwsNC(c);
end;
ConsistentAlphas := function()
  return Filtered(Tuples([0..4], 6), a -> IsConfluent(DescColl(a)));
end;
