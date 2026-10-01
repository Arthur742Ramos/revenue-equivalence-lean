module

public import Revenue.Defs
public import Mathlib.Tactic.Linarith

public section

namespace RevenueEquivalence

/-- Bayesian incentive compatibility makes the interim allocation rule monotone. -/
lemma X_monotone_of_BIC (X P : ℝ → ℝ) (h : BIC X P) : Monotone X := by
  intro s t hst
  by_cases heq : s = t
  · subst t
    exact le_rfl
  have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hst heq)
  have hts := bic_apply X P h t s
  have hst_bic := bic_apply X P h s t
  rw [interimUtility_apply] at hts hst_bic
  have hprod : 0 ≤ (t - s) * (X t - X s) := by
    nlinarith [hts, hst_bic]
  have hdiff : 0 ≤ X t - X s := by
    by_contra hnot
    have hneg : X t - X s < 0 := by linarith
    have hprod_neg : (t - s) * (X t - X s) < 0 :=
      mul_neg_of_pos_of_neg hpos hneg
    linarith
  linarith

/-- Under Bayesian incentive compatibility, the utility gap lies between the
type gap times the allocation at the lower and upper types. -/
lemma bic_sandwich (X P : ℝ → ℝ) (h : BIC X P) (s t : ℝ) (_hst : s ≤ t) :
    ((t - s) * X s ≤ interimUtility X P t - interimUtility X P s) ∧
      (interimUtility X P t - interimUtility X P s ≤ (t - s) * X t) := by
  have hts := bic_apply X P h t s
  have hst_bic := bic_apply X P h s t
  rw [interimUtility_apply] at hts hst_bic
  constructor
  · simp only [interimUtility_apply]
    nlinarith [hts]
  · simp only [interimUtility_apply]
    nlinarith [hst_bic]

end RevenueEquivalence
