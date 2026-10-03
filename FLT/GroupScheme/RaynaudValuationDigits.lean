/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDVRParameterValuation
public import FLT.GroupScheme.RaynaudFundamentalCycleParameters

/-!
# Binary valuations of the actual fundamental coefficients

Apply the proved complementary product to the actual cyclic presentation.
The unramified hypothesis is that p remains irreducible in the base DVR.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x) (e : F →+* ResidueField R)
  (r : ℕ+) (hr : Fintype.card F = p ^ (r : ℕ))


include h0 hadd in
/-- The actual fundamental coefficients have binary DVR valuation. -/
theorem FF.fundamentalCoefficient_valuation_digit (hp : Irreducible (p : R)) (i : Fin r) :
    IsDiscreteValuationRing.addVal R
      (X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr i) = 0 ∨
    IsDiscreteValuationRing.addVal R
      (X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr i) = 1 := by
  obtain ⟨b, u, hu⟩ := X.fundamentalCoefficient_complement lift h0 h1 hmul hadd
    p hdim hlift e r hr i
  exact (RaynaudParameters.dvr_valuation_digits hp u hu).imp And.left And.left

include h0 hadd in
/-- Each actual coefficient is a binary power of p times an integral unit. -/
theorem FF.fundamentalCoefficient_eq_prime_pow_mul_unit (hp : Irreducible (p : R))
    (i : Fin r) : ∃ (d : ℕ) (u : Rˣ), d ≤ 1 ∧
      X.fundamentalCoefficient lift h1 hmul p hdim hlift e r hr i = (p : R) ^ d * u := by
  obtain ⟨b, u, hu⟩ := X.fundamentalCoefficient_complement lift h0 h1 hmul hadd
    p hdim hlift e r hr i
  rcases RaynaudParameters.dvr_unit_or_uniformizer hp u hu with ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨0, h.unit, by omega, by simp⟩
  · obtain ⟨v, hv⟩ := h.symm
    exact ⟨1, v, le_rfl, by simpa using hv.symm⟩

end ThreeAdicPlan
