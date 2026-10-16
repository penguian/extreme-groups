#!/usr/bin/env python3
"""Join the exact isomorphism classes (iso_classes.txt) with the exhaustive per-presentation data
(exhaustive_5_7/all.txt); check that the invariants are constant on classes and summarise."""
import ast
import os
from collections import Counter, defaultdict

BASE = os.path.dirname(os.path.abspath(__file__)) + "/"


def typ(a):
    if (a[1] + a[5]) % 5:
        return "I"
    if a[2] == 0:
        return "II"
    if a[3] == 0:
        return "III"
    return "IV"


data = {}
for line in open(BASE + "exhaustive_5_7/all.txt"):
    f = line.strip().split(";")
    a = tuple(ast.literal_eval(f[0]))
    data[a] = dict(nextq=int(f[1]), ncand=int(f[2]), fS=int(f[3]),
                   maxf=int(f[5]), ncc=int(f[6]), z=int(f[7]))
assert len(data) == 625

classes = []
for line in open(BASE + "iso_classes.txt"):
    i, rep, t, osz, aut, orb = line.strip().split(";")
    orb = [tuple(x) for x in ast.literal_eval(orb)]
    classes.append(dict(i=int(i), rep=tuple(ast.literal_eval(rep)), aut=int(aut), orbit=orb))

assert sum(len(c["orbit"]) for c in classes) == 625
assert len(set(a for c in classes for a in c["orbit"])) == 625

bad = 0
rows = []
for c in classes:
    inv = {(data[a]["maxf"], data[a]["ncc"], data[a]["z"], data[a]["ncand"]) for a in c["orbit"]}
    if len(inv) != 1:
        bad += 1
        print("INVARIANT NOT CONSTANT on class", c["i"], inv)
    maxf, ncc, z, ncand = next(iter(inv))
    a3 = {a[2] for a in c["orbit"]}
    a4 = {a[3] for a in c["orbit"]}
    types = tuple(sorted(Counter(typ(a) for a in c["orbit"]).items()))
    extreme = 6 * maxf > 5 ** 7
    rows.append((c["i"], c["rep"], len(c["orbit"]), c["aut"], types, sorted(a3), sorted(a4),
                 maxf, ncc, extreme))

print("classes:", len(classes), " invariant violations:", bad)
print("alpha3 constant on every class:", all(len(r[5]) == 1 for r in rows))
print("extreme classes:", sum(r[9] for r in rows))
print("extreme <=> alpha3 in {2,3,4}:", all(r[9] == (r[5][0] in (2, 3, 4)) for r in rows))

summary = defaultdict(list)
for r in rows:
    summary[(r[9], r[7], r[8], tuple(t for t, _ in r[4]))].append(r)
print("\nextreme | max f | #cc | types met by the class's presentations | #classes | orbit sizes | |Aut| exps")
import math
for k in sorted(summary, key=lambda k: (-k[0], -k[1], k[3])):
    rs = summary[k]
    print(k[0], "|", k[1], "|", k[2], "|", "+".join(k[3]), "|", len(rs), "|",
          dict(Counter(r[2] for r in rs)), "|",
          dict(Counter(round(math.log(r[3], 5), 3) for r in rs)))

print("\nclasses per alpha3:", dict(Counter(r[5][0] for r in rows)))
print("classes that meet type IV:", sum(1 for r in rows if any(t == "IV" for t, _ in r[4])))
print("extreme classes with NO type IV presentation:",
      [r[1] for r in rows if r[9] and not any(t == "IV" for t, _ in r[4])])
