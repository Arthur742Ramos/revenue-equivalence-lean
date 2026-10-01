module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

public section

open MeasureTheory

namespace RevenueEquivalence

/-- interim utility of a bidder with type t facing interim allocation rule X and interim payment rule P (quasi-linear utility). -/
def interimUtility (X P : ℝ → ℝ) (t : ℝ) : ℝ := t * X t - P t

/-- Bayesian incentive compatibility, truthful reporting maximizes interim utility over all possible reports. -/
def BIC (X P : ℝ → ℝ) : Prop :=
  ∀ t r, t * X r - P r ≤ interimUtility X P t

/-- interim individual rationality, participation is weakly better than the outside option of zero. -/
def IIR (X P : ℝ → ℝ) : Prop := ∀ t, 0 ≤ interimUtility X P t

/-- ex ante expected payment under prior mu. -/
noncomputable def expectedPayment (P : ℝ → ℝ) (μ : MeasureTheory.Measure ℝ) : ℝ :=
  ∫ t, P t ∂μ

namespace Palomar

/-- Bayesian incentive compatibility gives the interval integral formula for the
change in interim utility from type zero to any nonnegative type. -/
public theorem envelope_integral (X P : ℝ → ℝ) (hBIC : BIC X P) (t : ℝ) (ht : 0 ≤ t) :
    interimUtility X P t - interimUtility X P 0 = ∫ x in (0 : ℝ)..t, X x := by
  sorry

/-- Bayesian incentive compatible mechanisms with the same allocation rule and
utility at type zero have equal payments at every nonnegative type. -/
public theorem revenueEquivalence (X P1 P2 : ℝ → ℝ) (h1 : BIC X P1) (h2 : BIC X P2)
    (hU : interimUtility X P1 0 = interimUtility X P2 0) (t : ℝ) (ht : 0 ≤ t) :
    P1 t = P2 t := by
  sorry

/-- Revenue equivalent mechanisms have equal expected payments under any measure
that assigns almost every type to the nonnegative reals. -/
public theorem expectedRevenueEqual (X P1 P2 : ℝ → ℝ) (μ : Measure ℝ)
    (h1 : BIC X P1) (h2 : BIC X P2)
    (hU : interimUtility X P1 0 = interimUtility X P2 0)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) :
    expectedPayment P1 μ = expectedPayment P2 μ := by
  sorry

end Palomar

end RevenueEquivalence
