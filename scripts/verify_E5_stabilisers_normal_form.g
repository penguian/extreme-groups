# verify_E5_stabilisers_normal_form.g  (11 Oct 2026)
# Cross-check of Lemma E (Report A §5.4(b)): in E5 = G/V every subgroup
#   T(k,j,b) = < x2*x3^k*x5^b , x4*x5^j >   (k,j,b in F_5)
# has order 25, is core-free, has f = 521, lies in E1 = <x2..x5>, and is conjugate to T_{k-j}.
Read("lib/alpha_lib.g");
alphas := ConsistentAlphas();
a := alphas[1]; G := DescGroup(a); x := AsList(Pcgs(G));
V := Subgroup(G, x{[6,7]}); hom := NaturalHomomorphismByNormalSubgroup(G, V);
E5q := Image(hom);
y := List([1..5], i -> Image(hom, x[i]));
E1 := Subgroup(E5q, y{[2..5]});
Fcount := function(E, T) return Size(Union(List(RightTransversal(E, T), g -> AsSet(T^g)))); end;
bad := 0; cnt := 0;
for k in [0..4] do for j in [0..4] do for b in [0..4] do
  T := Subgroup(E5q, [y[2]*y[3]^k*y[5]^b, y[4]*y[5]^j]);
  Tk := Subgroup(E5q, [y[4], y[2]*y[3]^((k-j) mod 5)]);
  cnt := cnt + 1;
  if not (Size(T) = 25 and Size(Core(E5q, T)) = 1 and Fcount(E5q, T) = 521
          and IsSubgroup(E1, T) and IsConjugate(E5q, T, Tk)) then
    bad := bad + 1;
  fi;
od; od; od;
Print("T(k,j,b) tested: ", cnt, "; failures: ", bad, "\n");
Print("|E5| = ", Size(E5q), ", exponent 5: ", Exponent(E5q) = 5, "\n");
QUIT;
