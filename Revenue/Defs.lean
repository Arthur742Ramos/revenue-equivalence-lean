module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

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

/-- Interim utility is the type-weighted allocation minus the payment. -/
lemma interimUtility_apply (X P : ℝ → ℝ) (t : ℝ) :
    interimUtility X P t = t * X t - P t := by
  rfl

/-- Bayesian incentive compatibility bounds the utility from every report by truthful utility. -/
lemma bic_apply (X P : ℝ → ℝ) (h : BIC X P) :
    ∀ t r, t * X r - P r ≤ interimUtility X P t := by
  intro t r
  exact h t r

end RevenueEquivalence
