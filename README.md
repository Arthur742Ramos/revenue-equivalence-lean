# Revenue equivalence theorem (Myerson 1981)

A Lean 4 + Mathlib formalization of Myerson's revenue equivalence theorem:
in a single-parameter setting with continuous real types and quasi-linear
utility, any two Bayesian incentive-compatible mechanisms that implement the
same interim allocation rule, and give the same interim utility to the lowest
type, charge the same interim payments at every nonnegative type — hence they
raise the same ex ante expected revenue under any prior supported on
nonnegative types.

## Headline result

Types are real numbers (`ℝ`), continuous. There is no finiteness assumption,
no independence assumption, no symmetry assumption, and no density assumption
on the prior. Utility is quasi-linear: a bidder of type `t` facing interim
allocation rule `X` and interim payment rule `P` gets
`interimUtility X P t = t * X t - P t`.

Bayesian incentive compatibility (`BIC X P`) means truthful reporting is
optimal at the interim stage:
`∀ t r, t * X r - P r ≤ interimUtility X P t`.

The three comparator theorems, in `RevenueEquivalence.Palomar`:

1. **Envelope formula** (`envelope_integral`):
   `(X P : ℝ → ℝ) (hBIC : BIC X P) (t : ℝ) (ht : 0 ≤ t)` gives
   `interimUtility X P t - interimUtility X P 0 = ∫ x in (0:ℝ)..t, X x`.
   Under BIC, the change in interim utility from type zero is pinned down by
   the interval integral of the allocation rule. The proof is a
   Riemann-sum-free squeeze: the BIC sandwich bounds both utility increments
   and integral pieces over a uniform `n`-partition of `[0, t]`; both
   telescoping sums share the same endpoint Riemann sums, whose gap is
   `(t / n) * (X t - X 0)`, forcing equality as `n → ∞`.

2. **Revenue equivalence** (`revenueEquivalence`):
   `(X P1 P2 : ℝ → ℝ) (h1 : BIC X P1) (h2 : BIC X P2)`
   `(hU : interimUtility X P1 0 = interimUtility X P2 0)`
   `(t : ℝ) (ht : 0 ≤ t)` gives `P1 t = P2 t`.
   Two BIC mechanisms with the same interim allocation rule and the same
   interim utility at type zero charge identical interim payments at every
   nonnegative type. Note the hypothesis is *equal* utility at type zero
   (`hU`), not zero utility; and interim individual rationality (`IIR`) is
   defined in the library but is *not* assumed by any of the three theorems.

3. **Expected revenue equality** (`expectedRevenueEqual`):
   `(X P1 P2 : ℝ → ℝ) (μ : Measure ℝ)` with the same BIC and type-zero
   hypotheses plus `(hsupp : ∀ᵐ t ∂μ, 0 ≤ t)` gives
   `expectedPayment P1 μ = expectedPayment P2 μ`,
   where `expectedPayment P μ = ∫ t, P t ∂μ` is the Bochner integral of the
   payment rule. The prior must be supported on nonnegative types almost
   everywhere.

All three theorems use only the axioms `propext`, `Classical.choice`, and
`Quot.sound`. The library (`Revenue/`) and `Solution.lean` contain zero
sorries; `Challenge.lean` carries three deliberate sorry placeholders for the
theorem statements, per the Palomar statement-surface format.

## Repository layout

- `Revenue/` — the Lean 4 proof library: `Defs.lean` (definitions and API
  lemmas), `BIC.lean` (monotonicity and the sandwich inequality),
  `Envelope.lean` (the envelope integral formula), `Equivalence.lean` (the
  main theorem and its expected-revenue corollary), `Main.lean` (entry point).
- `Challenge.lean`, `Solution.lean`, `comparator.json` — Palomar registry
  packaging. Challenge restates the four definitions with real bodies and the
  three theorems with sorry placeholders, importing only Mathlib. Solution
  proves the three `RevenueEquivalence.Palomar` theorems by applying the
  library. The two modules are compiled separately because their fully
  qualified statement names coincide.
- `formalization.yaml` — registry metadata. `M6_AUDIT.md` — the
  prose-to-hypothesis audit gating every factual claim below against the Lean
  artifact.
- `scripts/verify-palomar.sh` — local replica of the Palomar verification
  checks (module headers, builds, declaration kinds in both environments,
  axiom audits, the official `lake comparator` stage, whitespace).

## Prior formalizations

A Palomar registry API search on 2026-10-01 (via
`https://data.palomar-registry.org/api/v1/results`) returned zero entries for
`revenue equivalence`. The query `Myerson` returned one entry,
PALOMAR-2026-09-26-000002, the Myerson–Satterthwaite impossibility theorem —
a different theorem (inefficient bilateral trade is impossible), not revenue
equivalence. The query `auction` returned one entry,
PALOMAR-2026-10-01-000007 (Bulow–Klemperer), also a different theorem. These
are dated, limited observations, not universal prior-art claims.

## Build

Requires the Lean toolchain pinned in `lean-toolchain` (Lean/Mathlib
v4.35.0-rc2). Build with:

```
lake build
```

Run the local Palomar verification replica with:

```
scripts/verify-palomar.sh
```

## Author and license

Author and responsible maintainer: **Arthur Freitas Ramos**. License:
[BSD-3-Clause](LICENSE). AI assistance (GPT-6.1 via Codex) was used for the
formalization and packaging; every milestone was compiled and axiom-audited
independently. Acknowledgements: Mathlib contributors and Roger B. Myerson,
whose 1981 "Optimal auction design" (Mathematics of Operations Research 6(1),
58–73) is the source result.
