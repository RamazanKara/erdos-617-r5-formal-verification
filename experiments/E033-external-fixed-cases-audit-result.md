# E033 — independent audit of the external fixed-case repository

Completed: 2026-07-22 (Europe/Berlin)

Exact result: the external r=5 manuscript is an unrestricted
`CANDIDATE-RESOLUTION`. A complete line-by-line audit found no mathematical
gap, and independent finite checks corroborate every small classification used
by the proof. This is not a `MACHINE-VERIFIED-RESOLUTION` because the full
deduction, including the imported extremal theorem, has not been kernel-checked
or reduced to a complete certificate chain. It is not externally reviewed.
The all-\(r\) Erdős Problem 617 conjecture remains `OPEN` even if this fixed
case is correct.

## Source pin and public status

The audited repository is
`https://github.com/Robby955/erdos-617-fixed-cases` at commit
`735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab` (commit time
2026-07-21T16:20:01-05:00). The r=5 source first appeared in commit
`c19ce7e89ccdcd9b6c419c807ce6fbc3ce039679`; commit
`93a1b08c40a3627965acbb4163f501163f3228ee` made only audited exposition
clarifications and rebuilt the PDF. No later commit changes the r=5 proof.

Pinned hashes are:

- `r5/main.tex`, 43,626 bytes:
  `47ce42a3c7116f125bada1416e90d4f40a25ce5284362c98de3077bc51fcc769`;
- `r5/erdos-617-r5.pdf`, 402,508 bytes:
  `741106d5b4ce9cd08f406096907f7fb0678afd815ed7e703bae64717165b9c81`;
- `r5/references.bib`, 1,906 bytes:
  `d1f38f2e2deacb736db949309c22e7ac353f27d14d2c432f6c3692ed0b5aa2b4`.

The repository itself labels all five fixed-case manuscripts unreviewed
preprints. On 2026-07-22 the Erdős Problems page still marked Problem 617 open,
reported no partial or complete solution claim in its comments, and had last
been edited on 2026-04-01. Therefore neither site supplies independent review.

## Clean source reproduction

The TeX source was read in full. A fresh out-of-tree build with latexmk 4.88,
pdfTeX 1.40.29, BibTeX 0.99e, and TeX Live 2026 completed with no final
warnings after installing the declared `mathtools` package. The rebuilt
15-page PDF has SHA-256
`8c78a14a3c59eb204dc18b93ec40f9c34fb00b63f82551db16d88fd5e59c87e3`.
It is not byte-identical to the supplied PDF because the TeX/font environment
and creation metadata differ; byte identity of a derived PDF is not a proof
premise. Exact build data are in
`artifacts/external_r5_audit/build_receipt.json`.

## Imported theorem audit

The Kang--Pikhurko journal PDF was read in full and the relevant theorem,
construction, and optimizer pages were also visually inspected. Its SHA-256 is
`2f302962c5f018dc38478293df24f29429b832b061e252c19a7175598c65734e`.

- Theorem 1 has exactly the hypotheses used by the manuscript:
  \(n\ge r+3\), \(r\ge2\), and \(r\le(n-1)/2\), with maximum
  \(t_r(n)-\lfloor n/r\rfloor+1\) for a non-\(r\)-partite
  \(K_{r+1}\)-free graph.
- Theorem 4 says all extremal graphs arise from the displayed construction.
- Lemma 5 identifies the optimal part vectors. Independent integer
  optimization gives only \((4,5)\) at \((r,n)=(2,10)\), and only
  \((4,4,6)\), \((4,5,5)\) at \((3,15)\).
- All 20 oriented proper-subset templates at those endpoints were reconstructed
  independently. Every complement has a six-set with at least twelve edges,
  so equality is incompatible with the manuscript's local at-most-eleven
  condition.

Brooks's theorem is used only after the least color is forced to be
5-regular. No component is \(K_6\), and an odd-cycle exception cannot be
5-regular; a five-coloring would place at least six of 26 vertices in one
independent class. The hypotheses and conclusion match the standard theorem.

## Line-by-line proof-obligation ledger

Every item below was reconstructed without using the manuscript's conclusion.

1. **Color-graph translation — pass.** In a hypothetical balanced coloring,
   each color graph has one through eleven edges on every six-set, hence both
   independence and clique number at most five.
2. **Neighborhood accounting — pass.** For a minimum-degree vertex of degree
   \(d\), direct degree summation gives
   \(X+2Y\ge d(d-1)\) and \(X+Y\ge\binom d2\). At \(d=5\), local
   admissibility sharpens the latter to 14. Equality at \(d\le4\) isolates a
   \(K_{d+1}\).
3. **Initial minimum degree — pass.** The edge average, Brooks's theorem, and
   the checked Kang--Pikhurko bounds at orders 25 and 24 give
   \(2\le\delta\le4\) for a least color.
4. **Independence-two bounds — pass.** The degree argument for orders at least
   12 is correct. For order 11, an independent exhaustive catalog confirms
   that no triangle-free graph with at least 20 edges has at least four edges
   on every six-set; equivalently the color graph has at least 36 edges.
5. **Ten-vertex structure — pass.** Independent exhaustive enumeration gives
   exactly seven nonisomorphic triangle-free graphs satisfying the local
   four-edge condition: six bipartite graphs with 20 through 25 edges and one
   nonbipartite 20-edge graph. The latter is exactly the balanced two-fold
   blow-up of \(C_5\). Every 19-edge survivor has independence number at most
   four. The blow-up has vertex-cover number six, exactly five minimum covers,
   and distinct minimum covers intersect in at most four vertices.
6. **Independence-three obstruction — pass.** Every displayed degree table for
   orders 16, 17, and 18 was independently recomputed. The sole nonnumeric
   order-16 branch reduces correctly to the verified ten-vertex blow-up and a
   vertex cover of impossible size at most five. The order 19--22 values agree
   exactly with Kang--Pikhurko.
7. **Fifteen-vertex classifications — pass.** The minimum-degree-four split,
   bipartite escape branch, three-clique-cover contradiction, and equality
   accounting are exhaustive. The verified order-10 catalog gives exactly the
   stated 35-edge structure and the two stated 36-edge alternatives.
8. **Independence-four obstruction — pass.** All degree tables at orders 23,
   22, and 21 were recomputed. The order-21 degree-five branch treats the
   three-partite complement separately; the \(3^3-5\cdot3>0\) avoidance
   count is valid. The remaining branch reduces to the verified 15-vertex
   classification and the six-vertex-cover obstruction.
9. **Edge equalization — pass.** Counts at most 64 contradict the preceding
   obstruction for minimum degrees two, three, and four. Thus every color has
   at least 65 edges, and the sum \(5\cdot65=\binom{26}{2}\) forces equality
   in all five colors.
10. **Final recursion — pass.** The degree-two and degree-three routes force
    isolated \(K_3\) and \(K_4\) components and then contradict the audited
    lower tables. Degree four isolates a \(K_5\). Both possible residual
    minimum degrees are treated. Every subcase in the order-10 and order-15
    terminal splits either creates a forbidden \(K_6\), needs a cover of size
    at most five where six are necessary, or creates the explicitly counted
    fourteen-edge six-set. No residual branch is omitted.
11. **Sharp lower construction — pass.** The merged-slope affine coloring of
    \(K_{25}\) was independently rebuilt. All 177,100 six-sets contain all
    five colors, so the lower bound paired with the candidate upper proof is
    exactly \(R(6;5,4)=26\).

## Independent finite artifacts

Official nauty 2.9.3 `geng` (executable SHA-256
`478b5b9a503e1b17f42609085a0579e46f554a352ee16e396016b079ad973966`)
generated one representative of every nonisomorphic triangle-free graph in
the two endpoint spaces. A separate standard-library Python implementation
parses graph6 and checks every semantic property.

- Order 10: 12,172 graphs, raw catalog SHA-256
  `162cd507b93e74307ed9e88052da7bfb6f68e6cfeae6ccd2254c949c84ce0214`;
  compressed SHA-256
  `aa8c9ba9e9df4d07231cb1f5d72003664bbb577e1b56ac6af246fac526223a1b`.
- Order 11 with 20--30 edges: 6,153 graphs, raw catalog SHA-256
  `ce477f7ec1b99986993dd8386b7484dfd6378181eb29c292cf4b1a67157b7e61`;
  compressed SHA-256
  `1e8bff29631a7a3bb957aa0349e0138622c42917fde9b8a415bf387bc10e7e2e`.
- Independent checker:
  `tests/test_external_r5_proof_audit.py`, SHA-256
  `273478d11c6ca37d2212eeebb79869649058e248229eb44a1d1645c7a8141eb4`.

The command

```sh
python3 tests/test_external_r5_proof_audit.py
```

prints `EXTERNAL-R5-PROOF-AUDIT-PASS`, checks exact catalog and compression
hashes, validates every graph independently, reconstructs all 20 external
equality templates, recomputes the complete arithmetic chain, checks the
minimum-cover claims, and exhausts the affine construction.

## Exact conclusion and remaining obligations

No counterexample, invalid hypothesis, omitted branch, or false intermediate
lemma was found in the r=5 manuscript. The appropriate present label is
`CANDIDATE-RESOLUTION` for the unrestricted r=5 case. It is stronger evidence
than the prior exact-63 certificate frontier and pauses E032, but it does not
erase E032's value as an independent machine-certificate route.

Promotion to `MACHINE-VERIFIED-RESOLUTION` requires a kernel-checked
formalization or a complete equivalently explicit certificate pipeline for the
whole proof, especially the Kang--Pikhurko dependency and the theorem-to-model
bridge. Promotion to `EXTERNALLY-VERIFIED-RESOLUTION` additionally requires
qualified independent human review. The r=6,7,8,9 claims in the same external
repository were not audited in E033 and receive no verification upgrade here.
Even verification of all five fixed cases would not prove the all-\(r\)
conjecture.
