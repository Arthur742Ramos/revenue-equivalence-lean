module

public import Revenue.Envelope

public section

open MeasureTheory

namespace RevenueEquivalence

/-- Bayesian incentive compatible mechanisms with the same allocation rule and
utility at the reference type (type zero) have equal payments at every
nonnegative type. -/
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

/-- Revenue equivalent mechanisms whose interim payment rules are integrable
have equal (finite) expected payments under any prior that assigns almost
every type to the nonnegative reals. The integrability hypotheses make both
sides genuine expectations: Lean's Bochner integral is totalized, so without
them the equality would also hold vacuously for nonintegrable payment rules. -/
theorem expectedRevenueEqual (X P1 P2 : ℝ → ℝ) (μ : Measure ℝ)
    (h1 : BIC X P1) (h2 : BIC X P2)
    (hU : interimUtility X P1 0 = interimUtility X P2 0)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hInt1 : Integrable P1 μ) (hInt2 : Integrable P2 μ) :
    expectedPayment P1 μ = expectedPayment P2 μ := by
  have hP : ∀ᵐ t ∂μ, P1 t = P2 t := by
    filter_upwards [hsupp] with t ht
    exact revenueEquivalence X P1 P2 h1 h2 hU t ht
  -- The difference of the payment rules vanishes almost everywhere. Since both
  -- rules are integrable, the integral of the difference splits into the
  -- difference of the integrals, so both sides are finite expectations and
  -- their equality is not a vacuous totalized-integral identity.
  have hzero : (fun t => P1 t - P2 t) =ᵐ[μ] 0 := by
    filter_upwards [hP] with t ht
    exact sub_eq_zero.mpr ht
  have hsplit : ∫ t, (P1 t - P2 t) ∂μ
      = (∫ t, P1 t ∂μ) - ∫ t, P2 t ∂μ :=
    MeasureTheory.integral_sub hInt1 hInt2
  have h0 : ∫ t, (P1 t - P2 t) ∂μ = 0 :=
    MeasureTheory.integral_eq_zero_of_ae hzero
  rw [expectedPayment_apply, expectedPayment_apply]
  linarith [hsplit, h0]

end RevenueEquivalence
