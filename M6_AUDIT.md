# M6 audit: prose-to-hypothesis diff

Every factual claim in `README.md` and `formalization.yaml` is checked
against the Lean artifact. Each row quotes the exact declaration and its
binders, or marks the claim as non-Lean provenance (historical,
administrative, or dated search).

## P1: model claims

| Claim | Lean evidence |
| --- | --- |
| Types are ℝ, continuous, not finite | `RevenueEquivalence.interimUtility (X P : ℝ → ℝ) (t : ℝ) : ℝ`: every binder is `ℝ → ℝ` / `ℝ`. No `Fintype`, `Finite`, or `Nat` index appears in any definition or theorem. (`Revenue/Defs.lean`, `Challenge.lean`) |
| No independence / symmetry / density assumption | The only prior object is `μ : Measure ℝ` in `expectedPayment` and `expectedRevenueEqual`. No independence predicate, no symmetry hypothesis, no density function appears in any binder. |
| Quasi-linear utility | `def interimUtility (X P : ℝ → ℝ) (t : ℝ) : ℝ := t * X t - P t` |
| BIC is interim (Bayesian) | `def BIC (X P : ℝ → ℝ) : Prop := ∀ t r, t * X r - P r ≤ interimUtility X P t`: quantifies over true type `t` and report `r` at the interim stage. No dominant-strategy (ex post) quantifier. |
| IIR defined but not assumed | `def IIR (X P : ℝ → ℝ) : Prop := ∀ t, 0 ≤ interimUtility X P t` exists in `Revenue/Defs.lean`. None of `envelope_integral`, `revenueEquivalence`, `expectedRevenueEqual` (in `Revenue/Envelope.lean`, `Revenue/Equivalence.lean`, `Challenge.lean`, `Solution.lean`) takes an `IIR` hypothesis. |
| Expected payment is the Bochner integral | `noncomputable def expectedPayment (P : ℝ → ℝ) (μ : Measure ℝ) : ℝ := ∫ t, P t ∂μ` |

## P2: theorem claims

| Claim | Lean evidence |
| --- | --- |
| Envelope: BIC + `0 ≤ t` gives `U(t) − U(0) = ∫₀ᵗ X` | `theorem RevenueEquivalence.Palomar.envelope_integral (X P : ℝ → ℝ) (hBIC : BIC X P) (t : ℝ) (ht : 0 ≤ t) : interimUtility X P t - interimUtility X P 0 = ∫ x in (0:ℝ)..t, X x` (`Solution.lean`, applying `RevenueEquivalence.envelope_integral` from `Revenue/Envelope.lean`) |
| Revenue equivalence: equal type-zero utility (not zero utility) forces `P1 t = P2 t` on `0 ≤ t` | `theorem RevenueEquivalence.Palomar.revenueEquivalence (X P1 P2 : ℝ → ℝ) (h1 : BIC X P1) (h2 : BIC X P2) (hU : interimUtility X P1 0 = interimUtility X P2 0) (t : ℝ) (ht : 0 ≤ t) : P1 t = P2 t`. The hypothesis `hU` is an equality between the two mechanisms' type-zero utilities; neither side is asserted to be zero. |
| Expected-revenue corollary needs the prior supported on `≥ 0` a.e. and both payment rules integrable | `theorem RevenueEquivalence.Palomar.expectedRevenueEqual (X P1 P2 : ℝ → ℝ) (μ : Measure ℝ) (h1 : BIC X P1) (h2 : BIC X P2) (hU : interimUtility X P1 0 = interimUtility X P2 0) (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) (hInt1 : Integrable P1 μ) (hInt2 : Integrable P2 μ) : expectedPayment P1 μ = expectedPayment P2 μ`. The `hsupp`, `hInt1`, `hInt2` binders are quoted verbatim. The integrability hypotheses are load-bearing for the claim "expected revenue": Lean's Bochner integral is totalized, so without them the equality would also hold vacuously for nonintegrable payment rules. |
| Proof is a Riemann-sum-free squeeze | `Revenue/Envelope.lean`: uniform partition `p i = t * i / n`, per-interval bounds from `bic_sandwich` and `intervalIntegral.integral_mono_on`, telescoping via `Finset.sum_range_sub`, gap `(t / n) * (X t - X 0)` forced to zero by `exists_nat_gt` contradiction. No Riemann sum or virtual value appears. |
| Axioms ⊆ {propext, Classical.choice, Quot.sound} | `#print axioms` on all three `RevenueEquivalence.Palomar` theorems reports exactly `[propext, Classical.choice, Quot.sound]` (verified by `scripts/verify-palomar.sh`). |
| Zero sorries in library and Solution; 3 in Challenge | `grep` for `sorry` finds none in `Revenue/` or `Solution.lean`; exactly 3 in `Challenge.lean` (the theorem placeholders). The verify script enforces both counts. |

## P2b: totalization audit (all three theorems)

Lean's integrals are totalized (the Bochner integral of a nonintegrable
function is defined to be `0`; likewise the interval integral). Each
comparator theorem was audited for claims that would be vacuous without
integrability:

| Theorem | Integral in statement | Why it is meaningful |
| --- | --- | --- |
| `envelope_integral` | `∫ x in (0:ℝ)..t, X x` | Genuine finite integral: BIC implies the allocation rule is monotone (`lemma X_monotone_of_BIC (X P : ℝ → ℝ) (h : BIC X P) : Monotone X` in `Revenue/BIC.lean`), and a monotone function is interval-integrable on every interval (used in the proof of `RevenueEquivalence.envelope_integral` in `Revenue/Envelope.lean`). The prose claims only "the interval integral of the allocation rule", never "expected" anything. |
| `revenueEquivalence` | none (pointwise `P1 t = P2 t`) | No integral appears; no totalization issue possible. |
| `expectedRevenueEqual` | `∫ t, P t ∂μ` on both sides | Genuine finite expectations **only because** of the binders `(hInt1 : Integrable P1 μ) (hInt2 : Integrable P2 μ)`. Without them, the equality would also hold vacuously for nonintegrable payment rules (counterexample: `X t = t`, `P t = t^2 / 2` satisfy BIC, but a `1/n^2`-weighted prior on the nonnegative integers gives infinite payment expectation, and the totalized integral is `0`). The prose says "equal (finite) expected payments" and "for integrable payment rules" everywhere the corollary is described. |

## P3: packaging claims

| Claim | Evidence |
| --- | --- |
| Four comparator definitions are genuine defs | `comparator.json` lists `RevenueEquivalence.interimUtility`, `.BIC`, `.IIR`, `.expectedPayment`; the verify script checks `.defnInfo` for each in both the Challenge and Solution module environments. |
| Three comparator theorems | `comparator.json` lists `RevenueEquivalence.Palomar.envelope_integral`, `.revenueEquivalence`, `.expectedRevenueEqual`; checked as `.thmInfo` in both environments. |
| Challenge imports only Mathlib | `Challenge.lean` imports `Mathlib.MeasureTheory.Integral.Bochner.Basic` and `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` only; the verify script rejects any other import prefix and allowlists Challenge's transitive source deps. |
| Challenge and Solution compiled separately | `lakefile.toml` declares separate `[[lean_lib]]` entries; the two files never import each other. Their `RevenueEquivalence.Palomar.*` names coincide, which is why they must not be imported together. |

## P4: non-Lean provenance

| Claim | Provenance |
| --- | --- |
| Source result is Myerson (1981) "Optimal auction design", MOR 6(1), 58–73 | Historical/bibliographic fact; not a Lean claim. DOI 10.1287/moor.6.1.58 as published. |
| Registry search 2026-10-01: "revenue equivalence" → 0 entries | Performed via `https://data.palomar-registry.org/api/v1/results?q=revenue%20equivalence`; response `entries: []`, totals 390 results / 311 projects. Dated observation, not a universal absence claim. |
| "Myerson" → PALOMAR-2026-09-26-000002 (different theorem) | Same API, `q=Myerson`; the hit is the Myerson–Satterthwaite impossibility theorem (bilateral trade), not revenue equivalence. Cited to distinguish, not as related work on the same theorem. |
| "auction" → PALOMAR-2026-10-01-000007 (different theorem) | Same API, `q=auction`; the hit is Bulow–Klemperer (optimal auction vs second-price with an extra bidder), not revenue equivalence. |
| Author / maintainer Arthur Freitas Ramos; BSD-3-Clause | Administrative; matches `LICENSE` (Copyright (c) 2026 Arthur Freitas Ramos) and the git identity used for all commits. |
| AI assistance used; milestones independently compiled and axiom-audited | Process fact about this development session. |
| No Palomar submission or registration performed | True of this milestone; the intake is handled separately. |

## P5: claims deliberately NOT made

- Finite types, independent private values, symmetric bidders, positive densities: none appear in the artifact; none are claimed.
- IIR as a hypothesis of revenue equivalence: the artifact does not assume it; the prose explicitly notes it is defined but unused.
- Zero utility at the reference type (type zero): the artifact assumes equal (`hU`), not zero; the prose quotes `hU` verbatim. There is no lowest type in the model; zero is only the reference/normalization point.
- Multi-parameter settings or optimal-auction characterization: excluded in `fidelity.divergences`.
