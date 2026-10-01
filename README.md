# Myerson's revenue equivalence theorem

This project formalizes Myerson's revenue equivalence theorem (1981) in Lean 4
with Mathlib, in a finite single-parameter Bayesian mechanism-design model.

## Headline result

In a finite single-parameter setting with independent private types, any two
Bayesian incentive-compatible mechanisms that implement the same interim
allocation rule — and agree on expected payments at the lowest type — yield
the same interim expected payments for every type, hence the same expected
revenue. Expected revenue is pinned down by the allocation rule alone.

The formalization proves the payoff-equivalence / envelope lemma first:
under Bayesian incentive compatibility, each bidder's interim utility is
determined by the interim allocation rule together with the utility of the
lowest type. Revenue equivalence follows directly.

## Repository layout

- `Revenue/` — the Lean 4 formalization (definitions, envelope lemma, main theorem).
- `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml` —
  Palomar registry packaging (added at packaging time).
- `scripts/verify-palomar.sh` — local replica of the Palomar verification checks.

## Build

Requires the Lean toolchain pinned in `lean-toolchain`. Build with:

```
lake build
```

## License

BSD-3-Clause. See `LICENSE`.
