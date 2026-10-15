/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXCoefficients
public import FLT.Mazur.WeierstrassSuccessiveNilpotentSlopeMap
public import FLT.Mazur.WeierstrassSuccessiveNilpotentNodeChart

/-!
# The actual original node chart commutes with coefficient restriction

Restriction preserves all three coordinates and the constructed small slope.
Taking spectra gives the square of the original node open morphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- Change original coefficients while retaining the three actual chart coordinates. -/
def coefficientRingMap : Coordinate W s π b3 b4 b6 →+*
    Coordinate (W.map f) (f s) (f π) (f b3) (f b4) (f b6) := by
  letI := f.toAlgebra
  exact (coefficientMap W s π b3 b4 b6 S).toRingHom

/-- The successive coefficient restriction retains each named coordinate. -/
@[simp] theorem coefficientRingMap_coord (i : Fin 3) :
    coefficientRingMap f W s π b3 b4 b6 (coord W s π b3 b4 b6 i) =
      coord (W.map f) (f s) (f π) (f b3) (f b4) (f b6) i := by
  let _ := f.toAlgebra
  exact coefficientMap_coord W s π b3 b4 b6 S i

/-- Constants follow exactly the specified ring homomorphism. -/
@[simp] theorem coefficientRingMap_algebraMap (r : R) :
    coefficientRingMap f W s π b3 b4 b6 (algebraMap R _ r) = algebraMap S _ (f r) := by
  let _ := f.toAlgebra
  change (coefficientMap W s π b3 b4 b6 S).toRingHom (algebraMap R _ r) = _
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
    IsScalarTower.algebraMap_apply R S]
  rfl

/-- Constants and the original coordinates determine a ring homomorphism. -/
theorem coefficient_ringHom_ext {T : Type*} [CommRing T]
    (g h : Coordinate W s π b3 b4 b6 →+* T)
    (hc : ∀ r, g (algebraMap R _ r) = h (algebraMap R _ r))
    (hx : ∀ i, g (coord W s π b3 b4 b6 i) = h (coord W s π b3 b4 b6 i)) : g = h := by
  apply Ideal.Quotient.ringHom_ext
  exact MvPolynomial.ringHom_ext hc hx

variable (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (hf : I ≤ J.comap f) (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "ev" => nilpotentNodeRetraction W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "ev'" => nilpotentNodeRetraction (W.map f) (f s) (f π) (f b3) (f b4)
  (f b6) J hJ (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)

/-- The actual retraction commutes with restriction on coefficients and all coordinates. -/
theorem nilpotentNodeRetraction_map :
    (SuccessiveIncidence.coefficientRingMap f π).comp (ev).toRingHom =
      (ev').toRingHom.comp (coefficientRingMap f W s π b3 b4 b6) := by
  apply coefficient_ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, coefficientRingMap_algebraMap,
      SuccessiveIncidence.coefficientRingMap_algebraMap]
  · intro i
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      coefficientRingMap_coord, nilpotentNodeRetraction_coord]
    fin_cases i
    · exact SuccessiveIncidence.coefficientRingMap_t f π
    · exact nilpotentNodeSlope_map f W s π b3 b4 b6 I hI J hJ hf ha hs h2 h3 h4 h6
    · exact SuccessiveIncidence.coefficientRingMap_u f π

/-- The specified original node opens form a commuting square of scheme morphisms. -/
@[reassoc] theorem nilpotentNodeChart_restriction_square :
    Spec.map (CommRingCat.ofHom (SuccessiveIncidence.coefficientRingMap f π)) ≫
      nilpotentNodeChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 =
    nilpotentNodeChart (W.map f) (f s) (f π) (f b3) (f b4) (f b6) J hJ
      (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6) ≫
        Spec.map (CommRingCat.ofHom (coefficientRingMap f W s π b3 b4 b6)) := by
  simp only [nilpotentNodeChart, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g))
    (nilpotentNodeRetraction_map f W s π b3 b4 b6 I hI J hJ hf ha hs h2 h3 h4 h6)

end FLT.Mazur.WeierstrassSuccessiveX
