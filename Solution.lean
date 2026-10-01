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
utility at type zero have equal payments at every nonnegative type. -/
public theorem revenueEquivalence (X P1 P2 : ℝ → ℝ) (h1 : BIC X P1) (h2 : BIC X P2)
    (hU : interimUtility X P1 0 = interimUtility X P2 0) (t : ℝ) (ht : 0 ≤ t) :
    P1 t = P2 t :=
  _root_.RevenueEquivalence.revenueEquivalence X P1 P2 h1 h2 hU t ht

/-- Revenue equivalent mechanisms have equal expected payments under any measure
that assigns almost every type to the nonnegative reals. -/
public theorem expectedRevenueEqual (X P1 P2 : ℝ → ℝ) (μ : Measure ℝ)
    (h1 : BIC X P1) (h2 : BIC X P2)
    (hU : interimUtility X P1 0 = interimUtility X P2 0)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) :
    expectedPayment P1 μ = expectedPayment P2 μ :=
  _root_.RevenueEquivalence.expectedRevenueEqual X P1 P2 μ h1 h2 hU hsupp

end Palomar

end RevenueEquivalence
