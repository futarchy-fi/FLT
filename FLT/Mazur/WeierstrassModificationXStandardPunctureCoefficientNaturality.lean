/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentFactorCoefficientNaturality
public import FLT.Mazur.WeierstrassModificationXStandardPunctureEquiv
public import FLT.Mazur.NodalFiberPunctureCoefficientMap

/-!
# The full standard initial puncture is natural in its original coefficients

The coefficient square retains every localized function, including both
polynomial tangent corrections in the initial Laurent parameter change.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J)
  (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "F" => PolygonScalingNaturality.coeffMap f
local notation "U" => W.map f
local notation "N" => NodalFiber.Coordinate s
local notation "D" => Localization.Away (NodalFiber.p s)
local notation "N'" => NodalFiber.Coordinate (f s)
local notation "D'" => Localization.Away (NodalFiber.p (f s))
local notation "H₀" => laurentStandardPunctureEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "H₁" => laurentStandardPunctureEvaluation U (f s) (f b3) (f b4) (f b6) J hJ
  (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)
local notation "P" => NodalFiber.punctureCoefficientRingMap f s (f s) rfl true

/-- Every function on the complete initial puncture preserves the original coefficient map. -/
theorem laurentStandardPunctureEvaluation_coefficient :
    (F).comp (H₀).toRingHom = (H₁).toRingHom.comp P := by
  have hP (z : N) : P (algebraMap N D z) =
      algebraMap N' D' (NodalFiber.coefficientRingMap f s (f s) rfl z) :=
    NodalFiber.punctureCoefficientRingMap_base f s (f s) rfl true z
  apply IsLocalization.ringHom_ext (Submonoid.powers (NodalFiber.p s))
  apply NodalFiber.coefficient_ringHom_ext
  · intro a
    change F (H₀ (algebraMap N D (algebraMap R N a))) =
      H₁ (P (algebraMap N D (algebraMap R N a)))
    rw [hP,
      NodalFiber.coefficientRingMap_algebraMap,
      ← IsScalarTower.algebraMap_apply R N D,
      ← IsScalarTower.algebraMap_apply S N' D', AlgHom.commutes, AlgHom.commutes]
    exact PolygonScalingNaturality.coeffMap_C f a
  · change F (H₀ (algebraMap N D (NodalFiber.p s))) =
      H₁ (P (algebraMap N D (NodalFiber.p s)))
    rw [hP, NodalFiber.coefficientRingMap_p,
      laurentStandardPunctureEvaluation_p, laurentStandardPunctureEvaluation_p,
      map_mul, PolygonScalingNaturality.coeffMap_T_neg_one]
    exact congrArg (fun z ↦ LaurentPolynomial.T (-1) * z)
      (laurentOppositeFactor_coefficient f W s b3 b4 b6 I J hf hI hJ ha hs h2 h3 h4 h6 false)
  · change F (H₀ (algebraMap N D (NodalFiber.q s))) =
      H₁ (P (algebraMap N D (NodalFiber.q s)))
    rw [hP, NodalFiber.coefficientRingMap_q,
      laurentStandardPunctureEvaluation_q, laurentStandardPunctureEvaluation_q]
    exact laurentSmallFactor_coefficient f W s b3 b4 b6 I J hf hI hJ ha hs h2 h3 h4 h6 false

local notation "a₀" => initialStandardPunctureIso W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "a₁" => initialStandardPunctureIso U (f s) (f b3) (f b4) (f b6) J hJ
  (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)

attribute [local irreducible] laurentStandardPunctureEvaluation

/-- The original full standard initial puncture isomorphism commutes with coefficient change. -/
@[reassoc] theorem initialStandardPunctureIso_coefficient :
    Spec.map (CommRingCat.ofHom F) ≫ (a₀).hom =
      (a₁).hom ≫ Spec.map (CommRingCat.ofHom P) := by
  change Spec.map (CommRingCat.ofHom F) ≫ Spec.map (CommRingCat.ofHom (H₀).toRingHom) =
    Spec.map (CommRingCat.ofHom (H₁).toRingHom) ≫ Spec.map (CommRingCat.ofHom P)
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g ↦ Spec.map (CommRingCat.ofHom g))
    (laurentStandardPunctureEvaluation_coefficient f W s b3 b4 b6 I J hf hI hJ
      ha hs h2 h3 h4 h6)

end FLT.Mazur.WeierstrassModificationX
