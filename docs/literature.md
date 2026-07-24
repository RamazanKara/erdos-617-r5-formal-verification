# Literature and status audit

Access date for every web source in this file: **2026-07-20**, unless a later
date is stated explicitly.
The search is broad but cannot prove that no overlooked paper exists.

## Exact searches performed

The search included the required exact phrases “Erdős Problem 617”, “balanced
coloring complete graph”, “split and balanced colorings of complete graphs”, and
“five-coloring K26 every K6 all colors”, plus variants involving
`r^2+1`, `g_r(2)`, polychromatic colorings, Ramsey–Turán theory, dense
non-5-partite \(K_6\)-free graphs, formal conjectures, theses, GitHub, DOI
citations, and author publication pages.

Crossref reported 17 citations, Semantic Scholar 19, and OpenAlex 26 for the
1999 DOI. The differing counts illustrate database coverage differences. The 26
OpenAlex citing records were title-scanned; most concern split/adaptable/chromatic
capacity variants. No title or accessible text found in that pass claimed a
resolution of Conjecture 1. This is discovery evidence only, not a completeness
certificate for the literature.

## Newly located fixed-case preprints (2026-07-22 audit)

Robert Sneiderman, `Robby955/erdos-617-fixed-cases`,
[GitHub repository](https://github.com/Robby955/erdos-617-fixed-cases), audited
at commit `735c2eeffcb5c8abe92f8a6be04be2fa3c8bb6ab`. The repository claims the
fixed cases \(r=5,6,7,8,9\), explicitly says that none of the manuscripts has
completed external mathematical review, and explicitly does not claim the
all-\(r\) conjecture. The r=5 and r=6 arguments are presented as
non-computational; the higher cases use included finite verification packages.

E033 read the complete r=5 source and its complete Kang--Pikhurko dependency,
rebuilt the paper, reconstructed every proof step, and independently exhausted
the order-10 and order-11 triangle-free endpoint catalogs. No gap was found.
That E033 status was a `CANDIDATE-RESOLUTION`. E058 has since completed an
independent Lean and certificate verification and now supports
`MACHINE-VERIFIED-RESOLUTION` for fixed \(r=5\), but not
`EXTERNALLY-VERIFIED-RESOLUTION`: neither the upstream preprint nor this
formalization has completed independent expert review. The r=6--9 claims have
not been independently reproduced by this project and receive no upgraded
status here. Source, artifact, and checker hashes are recorded in
`experiments/E033-external-fixed-cases-audit-result.md` and
`experiments/E058-r5-special-brooks-kernel-bridge-result.md`.

On 2026-07-22 the [Erdős Problems page](https://www.erdosproblems.com/617)
still marked #617 open, said that there were no partial or complete solution
claims in its comments, and reported a last edit date of 2026-04-01. Thus the
new repository had not been incorporated into that status page and the page is
not independent review of the preprints.

A read-only recheck on 2026-07-24 found that the exact pinned GitHub README
still limits its claims to \(r=5,\ldots,9\), still says none has completed
external mathematical review, and still says those fixed cases do not settle
every \(r\). The Erdős Problems search index still returned #617 as open; the
direct page rejected the automated fetch with HTTP 403, so no newer page
content is inferred from that failed request. This is current-status context,
not proof evidence.

## Primary sources

### Erdős and Gyárfás (1999)

Paul Erdős and András Gyárfás, “Split and balanced colorings of complete
graphs,” *Discrete Mathematics* 200 (1999), 79–86,
[DOI](https://doi.org/10.1016/S0012-365X(98)00323-9),
[author-hosted PDF](https://www.renyi.hu/~gyarfas/Cikkek/92_splitandbalanced.pdf).

The PDF was read in full. It defines the balanced-coloring function, states the
all-\(r\) assertion as Conjecture 1, proves \(r=3,4\) in Lemmas 1 and 2, and
constructs balanced colorings on \(r^2\) vertices from affine planes for
infinitely many \(r\). The streamed PDF bytes had SHA-256
`3b21b6238428b30e7ee7241d8e0d8989ed0a28c839745aac4289145c722660cd`.
The proof reconstruction is in `docs/theory-notes.md`; the \(r=4\) proof has
not yet passed the project's independent-reproduction threshold.

### Gyárfás (2023; manuscript dated 2020)

András Gyárfás, “Problems close to my heart,” *European Journal of
Combinatorics* 111 (2023), 103695,
[DOI](https://doi.org/10.1016/j.ejc.2023.103695),
[repository PDF](https://real.mtak.hu/162708/1/ejc40.pdf).
Section 2.2 again states the assertion as Conjecture 2.4, explicitly noting it is
true for \(r=3,4\). This is strong later evidence from a conjecture's author that
the general problem remained open at manuscript time; it is not a guarantee about
all work after publication.

### Kang and Pikhurko (2005)

Mihyun Kang and Oleg Pikhurko, “Maximum \(K_{r+1}\)-free graphs which are
not \(r\)-partite,” *Matematychni Studii* 24 (2005), 12–20,
[DOI](https://doi.org/10.30970/ms.24.1.12-20),
[journal PDF](https://matstud.org.ua/texts/2005/24_1/24_1_012_020.pdf).
Their Theorem 1 gives, for \(n\ge r+3\) and \(r\le(n-1)/2\), the maximum
\(t_r(n)-\lfloor n/r\rfloor+1\) edges in a non-\(r\)-partite
\(K_{r+1}\)-free graph. At \((26,5)\) this is 266. The hypotheses have been
checked for `C-RED-003`. Theorem 4 and Lemma 5 also supply the complete extremal
families used in `C-EQ-002`. The downloaded PDF had SHA-256
`2f302962c5f018dc38478293df24f29429b832b061e252c19a7175598c65734e`.
The full proof is imported, not formalized locally.

### Hanson and Toft (1991)

D. Hanson and B. Toft, “k-Saturated Graphs of Chromatic Number at Least k,”
*Ars Combinatoria* 31 (1991), 159–164,
[publisher PDF](https://combinatorialpress.com/article/ars/Volume%20031/volume-31-paper-16.pdf).
The paper classifies the maximum-edge (k)-saturated graphs with chromatic
number at least (k). At (k=5,n=20) this recovers the same 146-edge
extremal frontier used above, but it does not classify the 145-edge case needed
for E009. All six scanned pages were rendered and visually inspected. The
downloaded PDF had SHA-256
`6abc20da0f96147f959decd3cd3fbdb8d9e534a60c28acdfc671addd4f9c714c`.

### Dirac (1957) and Kostochka--Stiebitz (2002)

G. A. Dirac, “A theorem of R. L. Brooks and a conjecture of H. Hadwiger,”
*Proceedings of the London Mathematical Society* s3-7 (1957), 161--195,
[DOI](https://doi.org/10.1112/plms/s3-7.1.161), proved the critical-graph edge
bound used in E029. The imported statement is: if (G\ne K_k) is a
(k)-color-critical graph and (k\ge4), then

\[
2e(G)\ge(k-1)|V(G)|+k-3.
\]

The exact statement, definition of (k)-color-critical, and its attribution
were independently checked on 2026-07-22 in Alexandr V. Kostochka and Michael
Stiebitz, “A list version of Dirac's theorem on the number of edges in
colour-critical graphs,” *Journal of Graph Theory* 39 (2002), 165--177,
[DOI](https://doi.org/10.1002/jgt.998),
[author-hosted PDF](https://kostochk.web.illinois.edu/docs/2004/jgt02s.pdf).
All 13 pages were rendered and visually inspected. The downloaded PDF had
SHA-256
`cbca4a02094bf51b54018857bf92e75a342fee594567b40fb8485c712a888027`.
Theorem 1 states the displayed ordinary-coloring result, while Theorem 2 proves
a stronger list/hypergraph version. E029 uses only Theorem 1 at (k=6). The
proof is imported rather than formalized locally.

### Kostochka and Yancey (2014)

Alexandr V. Kostochka and Matthew Yancey, “Ore's conjecture on color-critical
graphs is almost true,” *Journal of Combinatorial Theory, Series B* 109 (2014),
73--101, [DOI](https://doi.org/10.1016/j.jctb.2014.05.002),
[arXiv:1209.1050](https://arxiv.org/abs/1209.1050).
Theorem 3 states that every (k)-critical graph (G) satisfies

\[
|E(G)|\ge
\left\lceil
\frac{(k+1)(k-2)|V(G)|-k(k-3)}{2(k-1)}
\right\rceil.
\]

The arXiv PDF was downloaded and independently audited on 2026-07-22. All 28
pages were rendered and visually inspected, and the theorem statement was
checked against both extracted text and the rendered theorem page. Its
SHA-256 was
`e961dcdf544f74d570542f8aade58a0bc0ba61ad82decb6aa8ee11edf429e07f`.
E030 uses only the specialization (k=6) for critical subgraphs on at least 13
vertices. The published proof is imported rather than formalized locally.

### Kostochka and Yancey, equality characterization (2018)

Alexandr V. Kostochka and Matthew Yancey, “A Brooks-Type Result for Sparse
Critical Graphs,” *Combinatorica*,
[author-hosted PDF](https://kostochk.web.illinois.edu/docs/submit/cca18y.pdf).
The manuscript records receipt on 2012-12-13 and revision on 2017-03-24. Its
Theorem 6 states that for every (k\ge4), a (k)-critical graph attains the
Kostochka--Yancey edge bound exactly if and only if it is a (k)-Ore graph,
where (k)-Ore graphs are obtained from copies of (K_k) by DHGO compositions.

The 48-page primary PDF was downloaded independently on 2026-07-22. The
statement and surrounding definitions were checked in extracted text, and PDF
page 4 containing Theorem 6 was rendered and visually inspected. The bytes had
SHA-256
`9fb3f9169187a99188a6889cd92507d020d96425926ff85af385a7778a03eb50`.
E031 applies the equality direction only at (k=6,n=16,e=43), after separately
proving that the entire residual graph is 6-critical. The published proof is
imported rather than locally formalized.

## Secondary/current-status sources

The [Erdős Problems #617 page](https://www.erdosproblems.com/617), last edited
2026-04-01, labels the problem `FALSIFIABLE` and open, says the paper proves
\(r=3,4\), and reports no partial or complete solution in its comment activity.
This is a curated secondary source and explicitly warns that its status may be
incomplete.

The [Formal Conjectures Lean file](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/617.lean)
gives a useful formal statement using `Sym2 V → Fin r`, but as accessed it ends
the all-\(r\), \(r=3\), \(r=4\), and \(r^2\) declarations with `sorry`.
It is therefore a statement registry, not verified evidence for any of those
claims.

## Citation-neighborhood assessment

Direct citations include work on finite-basis split colorings, splittable
colorings, chromatic capacity, adaptable coloring, and polychromatic factors.
Those accessible items use related terminology but do not visibly settle this
specific \(r^2+1\) conjecture. “Unsolved graph colouring problems” (2015)
cites the source, but the accessible text found in this pass did not provide a
new theorem about #617. A future run should inspect every full citing text rather
than relying on title and search-snippet triage.
