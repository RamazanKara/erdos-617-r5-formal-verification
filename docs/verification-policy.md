# Verification policy

The governing levels and language in `RESEARCH_GOAL.md` apply without dilution.
In particular, search failure, solver agreement, and a structured-family UNSAT
result are not evidence of unrestricted impossibility.

For explicit colorings, the minimum acceptance chain is: strict scope-locked
format, content hash, exhaustive semantic enumeration by both the Python and C
checkers, deliberate bad-artifact rejection, and a human proof that checker
acceptance matches the original statement. A \(K_{26}\) candidate would then
require a formal theorem or equivalently explicit kernel-checked bridge before a
resolution label is used.

For a decisive UNSAT claim, no upgrade is allowed without a deterministic
unrestricted instance generator, proved encoding correspondence, complete branch
coverage, hashes, LRAT or an equivalently auditable certificate, and an independent
checker. A bounded UNSAT lemma requires the same chain over its exact stated
scope. The local-equality claim meets the bounded standard: its symmetry
completeness is proved, its CNF and LRAT are committed and hashed, and two
independent checkers accept while rejecting damaged proofs. This certifies only a
necessary equality-case incidence system. It is not an unrestricted \(K_{26}\)
UNSAT claim and cannot support a resolution label.

Every command in `make verify` is deterministic. Expected scope is supplied on
the command line, outputs used as evidence are committed and hashed, and temporary
regeneration is byte-compared. Binary build products are not evidence and are
excluded from version control; generated E058 Lean sources are retained because
they are reviewable proof source and are byte-bound to the final receipt. Solver
output is reproducible through an optional pinned `python-sat==1.9.dev7` path,
but the normal verification path consumes only the proof certificate and does
not import or trust the solver.

E058 meets the decisive fixed-\(r=5\) standard. The final declaration
`Erdos617.e058Problem617AtFive : Problem617At 5` is unconditional in the
pinned Lean kernel. Its exact audited dependencies are `propext`,
`Classical.choice`, and `Quot.sound`; the 89 certificate theorems are connected
to graph semantics and complete symmetry coverage inside Lean. This supports
`MACHINE-VERIFIED-RESOLUTION` only for fixed \(r=5\). It does not promote
fixed \(r=6,\ldots,9\), the all-\(r\) conjecture, or an external-review label.

Performance and reproducibility diagnostics remain separate from logical
evidence. In particular, the preregistered unreduced branch-02 proof-only
benchmark timed out at its 300-second cap; that failure is retained and
reported, while the theorem-bearing reduced proof passed the kernel audits.
No speedup ratio is inferred from the failed raw run.

OpenAI Codex materially assisted source drafting, automation, execution, and
documentation. AI-generated assertions are never evidence; only the retained
proof sources, certificates, kernel outputs, audits, and hashes support the
claim. See `AI_USAGE.md`.
