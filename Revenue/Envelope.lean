module

public import Revenue.BIC
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

namespace RevenueEquivalence

open MeasureTheory

/-- Under Bayesian incentive compatibility, interim utility at a nonnegative type
equals utility at type zero plus the interval integral of the allocation rule.
The proof squeezes utility and the integral between common finite endpoint sums. -/
theorem envelope_integral (X P : ℝ → ℝ) (hBIC : BIC X P) (t : ℝ) (ht : 0 ≤ t) :
    interimUtility X P t - interimUtility X P 0 = ∫ x in (0:ℝ)..t, X x := by
  rcases eq_or_lt_of_le ht with rfl | hpos
  · simp [intervalIntegral.integral_same]
  have hXmono : Monotone X := X_monotone_of_BIC X P hBIC
  have hXint : ∀ a b : ℝ, IntervalIntegrable X volume a b :=
    fun a b => Monotone.intervalIntegrable hXmono
  suffices hD :
      (interimUtility X P t - interimUtility X P 0) -
        (∫ x in (0:ℝ)..t, X x) = 0 by
    linarith
  have key : ∀ n : ℕ, 1 ≤ n →
      |(interimUtility X P t - interimUtility X P 0) -
        (∫ x in (0:ℝ)..t, X x)| ≤ (t / (n : ℝ)) * (X t - X 0) := by
    intro n hn
    have hnpos : 0 < n := by omega
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    set p : ℕ → ℝ := fun i => t * (i : ℝ) / (n : ℝ) with hp_def
    have hp0 : p 0 = 0 := by simp [hp_def]
    have hpn : p n = t := by
      simp only [hp_def]
      field_simp [ne_of_gt hnR]
    have hpdiff : ∀ i : ℕ, p (i + 1) - p i = t / (n : ℝ) := by
      intro i
      have hcast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by
        push_cast
        ring
      simp only [hp_def, hcast]
      ring
    have hple : ∀ i : ℕ, p i ≤ p (i + 1) := by
      intro i
      have hnonneg : 0 ≤ t / (n : ℝ) := div_nonneg ht hnR.le
      linarith [hpdiff i]
    have hsand : ∀ i ∈ Finset.range n,
        (t / (n:ℝ)) * X (p i) ≤
          interimUtility X P (p (i + 1)) - interimUtility X P (p i) ∧
        interimUtility X P (p (i + 1)) - interimUtility X P (p i) ≤
          (t / (n:ℝ)) * X (p (i + 1)) := by
      intro i hi
      have h := bic_sandwich X P hBIC (p i) (p (i + 1)) (hple i)
      rwa [hpdiff i] at h
    have htelU :
        ∑ i ∈ Finset.range n,
          (interimUtility X P (p (i + 1)) - interimUtility X P (p i)) =
        interimUtility X P t - interimUtility X P 0 := by
      have h := Finset.sum_range_sub (fun i : ℕ => interimUtility X P (p i)) n
      simp only [hpn, hp0] at h
      exact h
    have hUlow :
        ∑ i ∈ Finset.range n, (t / (n:ℝ)) * X (p i) ≤
          interimUtility X P t - interimUtility X P 0 := by
      rw [← htelU]
      exact Finset.sum_le_sum fun i hi => (hsand i hi).1
    have hUhigh :
        interimUtility X P t - interimUtility X P 0 ≤
          ∑ i ∈ Finset.range n, (t / (n:ℝ)) * X (p (i + 1)) := by
      rw [← htelU]
      exact Finset.sum_le_sum fun i hi => (hsand i hi).2
    have hsplit : ∀ i : ℕ,
        (∫ x in (0:ℝ)..(p (i + 1)), X x) - (∫ x in (0:ℝ)..(p i), X x) =
          ∫ x in (p i)..(p (i + 1)), X x := by
      intro i
      have h := intervalIntegral.integral_add_adjacent_intervals
        (hXint 0 (p i)) (hXint (p i) (p (i + 1)))
      linarith
    have htelI :
        ∑ i ∈ Finset.range n, (∫ x in (p i)..(p (i + 1)), X x) =
          ∫ x in (0:ℝ)..t, X x := by
      have h := Finset.sum_range_sub
        (fun i : ℕ => ∫ x in (0:ℝ)..(p i), X x) n
      simp only [hpn, hp0, intervalIntegral.integral_same, sub_zero] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => (hsplit i).symm
    have hconst : ∀ i : ℕ, ∀ c : ℝ,
        (∫ _ in (p i)..(p (i + 1)), c) = (t / (n:ℝ)) * c := by
      intro i c
      rw [intervalIntegral.integral_const, smul_eq_mul, hpdiff i]
    have hint : ∀ i ∈ Finset.range n,
        (t / (n:ℝ)) * X (p i) ≤ (∫ x in (p i)..(p (i + 1)), X x) ∧
        (∫ x in (p i)..(p (i + 1)), X x) ≤ (t / (n:ℝ)) * X (p (i + 1)) := by
      intro i hi
      have h2 : IntervalIntegrable X volume (p i) (p (i + 1)) := hXint _ _
      have hbeta : ∀ c : ℝ,
          (∫ u in (p i)..(p (i + 1)), (fun _ => c) u) =
            (∫ _ in (p i)..(p (i + 1)), c) := fun c => rfl
      constructor
      · have hmono : ∀ x ∈ Set.Icc (p i) (p (i + 1)), X (p i) ≤ X x :=
          fun x hx => hXmono hx.1
        have hle_int := intervalIntegral.integral_mono_on
          (f := fun _ => X (p i)) (g := X) (μ := volume)
          (hple i) intervalIntegrable_const h2 hmono
        rw [hbeta (X (p i)), hconst i] at hle_int
        exact hle_int
      · have hmono : ∀ x ∈ Set.Icc (p i) (p (i + 1)), X x ≤ X (p (i + 1)) :=
          fun x hx => hXmono hx.2
        have hle_int := intervalIntegral.integral_mono_on
          (f := X) (g := fun _ => X (p (i + 1))) (μ := volume)
          (hple i) h2 intervalIntegrable_const hmono
        rw [hbeta (X (p (i + 1))), hconst i] at hle_int
        exact hle_int
    have hIlow :
        ∑ i ∈ Finset.range n, (t / (n:ℝ)) * X (p i) ≤
          ∫ x in (0:ℝ)..t, X x := by
      rw [← htelI]
      exact Finset.sum_le_sum fun i hi => (hint i hi).1
    have hIhigh :
        (∫ x in (0:ℝ)..t, X x) ≤
          ∑ i ∈ Finset.range n, (t / (n:ℝ)) * X (p (i + 1)) := by
      rw [← htelI]
      exact Finset.sum_le_sum fun i hi => (hint i hi).2
    have hdiff :
        (∑ i ∈ Finset.range n, (t / (n:ℝ)) * X (p (i + 1))) -
          (∑ i ∈ Finset.range n, (t / (n:ℝ)) * X (p i)) =
        ∑ i ∈ Finset.range n, (t / (n:ℝ)) * (X (p (i + 1)) - X (p i)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hfactor :
        ∑ i ∈ Finset.range n, (t / (n:ℝ)) * (X (p (i + 1)) - X (p i)) =
          (t / (n:ℝ)) * (X t - X 0) := by
      rw [← Finset.mul_sum]
      congr 1
      have h := Finset.sum_range_sub (fun i : ℕ => X (p i)) n
      simp only [hpn, hp0] at h
      exact h
    rw [← hfactor, ← hdiff, abs_le]
    constructor <;> linarith [hUlow, hUhigh, hIlow, hIhigh]
  have hC : (0:ℝ) ≤ X t - X 0 := sub_nonneg.mpr (hXmono ht)
  by_contra hne
  have hDpos :
      0 < |(interimUtility X P t - interimUtility X P 0) -
        (∫ x in (0:ℝ)..t, X x)| := abs_pos.mpr hne
  obtain ⟨m, hm⟩ := exists_nat_gt
    (t * (X t - X 0) /
      |(interimUtility X P t - interimUtility X P 0) - (∫ x in (0:ℝ)..t, X x)|)
  have hratio : 0 ≤ t * (X t - X 0) /
      |(interimUtility X P t - interimUtility X P 0) - (∫ x in (0:ℝ)..t, X x)| :=
    div_nonneg (mul_nonneg ht hC) hDpos.le
  have hmR : (0:ℝ) < (m:ℝ) := lt_of_le_of_lt hratio hm
  have hmpos : 1 ≤ m := by
    have hmnat : 0 < m := by exact_mod_cast hmR
    omega
  have hle := key m hmpos
  have e1 : t * (X t - X 0) <
      (m:ℝ) * |(interimUtility X P t - interimUtility X P 0) -
        (∫ x in (0:ℝ)..t, X x)| := by
    have h := mul_lt_mul_of_pos_right hm hDpos
    rw [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h
    exact h
  have hcancel : ((t / (m:ℝ)) * (X t - X 0)) * (m:ℝ) = t * (X t - X 0) := by
    field_simp [ne_of_gt hmR]
  have e2 :
      |(interimUtility X P t - interimUtility X P 0) -
        (∫ x in (0:ℝ)..t, X x)| * (m:ℝ) ≤ t * (X t - X 0) := by
    have h := mul_le_mul_of_nonneg_right hle hmR.le
    rw [hcancel] at h
    exact h
  have e3 :
      (m:ℝ) * |(interimUtility X P t - interimUtility X P 0) -
        (∫ x in (0:ℝ)..t, X x)| =
      |(interimUtility X P t - interimUtility X P 0) -
        (∫ x in (0:ℝ)..t, X x)| * (m:ℝ) := mul_comm _ _
  linarith

end RevenueEquivalence
