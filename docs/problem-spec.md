# Mathematical and executable specification

## Full conjecture versus the finite frontier

For every integer \(r\ge3\), the conjecture says that every map
\[
\kappa:\binom{[r^2+1]}2\to[r]
\]
has a set \(S\) of \(r+1\) vertices and a color \(c\) such that
\(\kappa(e)\ne c\) for every \(e\in\binom S2\).

A counterexample for one value of \(r\) disproves the full conjecture. A positive
proof for \(r=5\) proves only that finite case.

For \(r=5\), vertices are `0,...,25` and colors are `0,...,4`. A balanced
coloring is a total function on the 325 unordered pairs satisfying
\[
\forall S\in\binom{[26]}6\;\forall c\in[5]\;\exists\{u,v\}\in\binom S2:
\kappa(\{u,v\})=c.
\]
There are \(\binom{26}{6}=230230\) six-sets. An explicit coloring satisfying
this formula would be a negative resolution of the full all-\(r\) conjecture.

## Artifact format

The strict ASCII format is:

```text
ERDOS617-COLORING-V1 n r k
0 1 color
0 2 color
...
n-2 n-1 color
```

Exactly \(\binom n2\) records follow the header, one for every `u v` in
lexicographic order with `0 <= u < v < n`. Each color is an integer in
`0,...,r-1`. Comments, omitted edges, duplicate edges, reordered edges, extra
tokens, and trailing records are rejected. Verification commands require the
expected `(n,r,k)` separately, so an artifact cannot weaken its own scope by
changing its header.

## Checker correspondence

After strict parsing, each checker stores exactly one color for every unordered
pair. It enumerates every increasing \(k\)-tuple, ORs one bit for each of its
\(\binom k2\) edge colors, and accepts exactly when the result is
`(1 << r) - 1` for every tuple. Thus acceptance is equivalent, term by term,
to the quantified formula above. The Python checker uses
`itertools.combinations`; the C checker uses an independent in-place successor
algorithm for increasing tuples.

The committed \(K_{25}\) sharpness artifact deliberately uses header
`(25,5,6)` and is never presented as evidence for `(26,5,6)`.

## Graph formulation

For each color \(c\), let \(G_c\) contain exactly the color-\(c\) edges and
let \(H_c=\overline{G_c}\) inside the same complete graph. The executable
property is equivalent to \(\alpha(G_c)\le5\), or equivalently that \(H_c\)
is \(K_6\)-free, for every \(c\). This equivalence is proved in
`docs/theory-notes.md`.
