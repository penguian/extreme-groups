# For ALL 625 consistent alphas: check
#  (1) [x4, x2*x3^k] = x6 * x7^(a2 + k*a4)      (2) (x2*x3^k)^5 = x6^4 * x7^(a6 - k)
#  (3) for a3<>0, k0 = (a2+a6)/a3 mod 5 gives |<x4, x2*x3^k0>| = 125 ; and for all other k it is 625
Read("lib/alpha_lib.g");
alphas := ConsistentAlphas();
Print("number of consistent alphas: ", Length(alphas), "\n");
bad1 := 0; bad2 := 0; bad3 := 0; n3 := 0; mism := [];
for a in alphas do
  G := DescGroup(a); gg := GeneratorsOfGroup(G); pcgs := Pcgs(G);
  for k in [0..4] do
    s1 := gg[2]*gg[3]^k; s2 := gg[4];
    e1 := ExponentsOfPcElement(pcgs, Comm(s2,s1));
    e2 := ExponentsOfPcElement(pcgs, s1^5);
    if e1 <> [0,0,0,0,0,1,(a[2]+k*a[4]) mod 5] then bad1 := bad1+1; fi;
    if e2 <> [0,0,0,0,0,4,(a[6]-k) mod 5] then bad2 := bad2+1; fi;
  od;
  if a[3] <> 0 then
    n3 := n3+1;
    k0 := ((a[2]+a[6]) * (1/a[3] mod 5)) mod 5;
    for k in [0..4] do
      sz := Size(Subgroup(G, [gg[2]*gg[3]^k, gg[4]]));
      if (k = k0 and sz <> 125) or (k <> k0 and sz <> 625) then bad3 := bad3+1; Add(mism,[a,k,sz]); fi;
    od;
  fi;
od;
Print("violations of (1): ", bad1, ", of (2): ", bad2, ", of (3): ", bad3, " over ", n3, " alphas with a3<>0\n");
Print("mismatches: ", Length(mism), "\n");
if Length(mism) > 0 then Print(mism{[1..Minimum(5,Length(mism))]}, "\n"); fi;
Print("finished\n");
QUIT;
