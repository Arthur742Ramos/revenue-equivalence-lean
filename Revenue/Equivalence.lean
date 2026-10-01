module

public import Revenue.Envelope

public section

open MeasureTheory

namespace RevenueEquivalence

/-- Bayesian incentive compatible mechanisms with the same allocation rule and
utility at type zero have equal payments at every nonnegative type. -/
theorem revenueEquivalence (X P1 P2 : ℝ → ℝ) (h1 : BIC X P1) (h2 : BIC X P2)
    (hU : interimUtility X P1 0 = interimUtility X P2 0) (t : ℝ) (ht : 0 ≤ t) :
    P1 t = P2 t := by
  have e1 : interimUtility X P1 t - interimUtility X P1 0 =
      ∫ x in (0:ℝ)..t, X x := envelope_integral X P1 h1 t ht
  have e2 : interimUtility X P2 t - interimUtility X P2 0 =
      ∫ x in (0:ℝ)..t, X x := envelope_integral X P2 h2 t ht
  have hUt : interimUtility X P1 t = interimUtility X P2 t := by
    linarith [e1, e2, hU]
  rw [interimUtility_apply, interimUtility_apply] at hUt
  linarith [hUt]

/-- Revenue equivalent mechanisms have equal expected payments under any measure
that assigns almost every type to the nonnegative reals. -/
theorem expectedRevenueEqual (X P1 P2 : ℝ → ℝ) (μ : Measure ℝ)
    (h1 : BIC X P1) (h2 : BIC X P2)
    (hU : interimUtility X P1 0 = interimUtility X P2 0)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) :
    expectedPayment P1 μ = expectedPayment P2 μ := by
  have hP : ∀ᵐ t ∂μ, P1 t = P2 t := by
    filter_upwards [hsupp] with t ht
    exact revenueEquivalence X P1 P2 h1 h2 hU t ht
  rw [expectedPayment_apply, expectedPayment_apply]
  exact MeasureTheory.integral_congr_ae hP

end RevenueEquivalence
