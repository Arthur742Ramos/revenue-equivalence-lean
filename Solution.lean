module

public import Revenue.Main

public section

open MeasureTheory

namespace RevenueEquivalence

namespace Palomar

/-- Bayesian incentive compatibility gives the interval integral formula for the
change in interim utility from type zero to any nonnegative type. -/
public theorem envelope_integral (X P : ℝ → ℝ) (hBIC : BIC X P) (t : ℝ) (ht : 0 ≤ t) :
    interimUtility X P t - interimUtility X P 0 = ∫ x in (0 : ℝ)..t, X x :=
  _root_.RevenueEquivalence.envelope_integral X P hBIC t ht

/-- Bayesian incentive compatible mechanisms with the same allocation rule and
utility at the reference type (type zero) have equal payments at every
nonnegative type. -/
public theorem revenueEquivalence (X P1 P2 : ℝ → ℝ) (h1 : BIC X P1) (h2 : BIC X P2)
    (hU : interimUtility X P1 0 = interimUtility X P2 0) (t : ℝ) (ht : 0 ≤ t) :
    P1 t = P2 t :=
  _root_.RevenueEquivalence.revenueEquivalence X P1 P2 h1 h2 hU t ht

/-- Revenue equivalent mechanisms whose interim payment rules are integrable
have equal (finite) expected payments under any prior that assigns almost
every type to the nonnegative reals. -/
public theorem expectedRevenueEqual (X P1 P2 : ℝ → ℝ) (μ : Measure ℝ)
    (h1 : BIC X P1) (h2 : BIC X P2)
    (hU : interimUtility X P1 0 = interimUtility X P2 0)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hInt1 : Integrable P1 μ) (hInt2 : Integrable P2 μ) :
    expectedPayment P1 μ = expectedPayment P2 μ :=
  _root_.RevenueEquivalence.expectedRevenueEqual X P1 P2 μ h1 h2 hU hsupp hInt1 hInt2

end Palomar

end RevenueEquivalence
