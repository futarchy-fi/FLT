/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFactorRatioLaurentEquiv
public import FLT.Mazur.WeierstrassModificationXLaurentFactorCoefficientNaturality
public import FLT.Mazur.WeierstrassModificationXInitialMobiusNormalization

/-!
# Coefficient squares for the corrected squared-factor Laurent parameter

Both the exact unit and the inverse algebra automorphism commute with the
original coefficient restriction at arbitrary nilpotent order.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s : R)
  (b3 b4 b6 : R) (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "F" => PolygonScalingNaturality.coeffMap f
local notation "u" => factorRatioLaurentUnit W ha s b3 b4 b6 I hI hs h2 h3 h4 h6
local notation "u'" => factorRatioLaurentUnit (W.map f) (ha.map f) (f s)
  (f b3) (f b4) (f b6) J hJ (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)
local notation "e" => factorRatioLaurentEquiv W ha s b3 b4 b6 I hI hs h2 h3 h4 h6
local notation "e'" => factorRatioLaurentEquiv (W.map f) (ha.map f) (f s)
  (f b3) (f b4) (f b6) J hJ (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)

/-- The complete original retained unit follows coefficient change, with every correction. -/
theorem factorRatioLaurentUnit_coefficient : Units.map (F).toMonoidHom u = u' := by
  apply Units.ext
  change F (u : R[T;T⁻¹]) = (u' : S[T;T⁻¹])
  rw [factorRatioLaurentUnit_coe, factorRatioLaurentUnit_coe, map_mul, map_mul, map_pow, map_pow]
  have hi := congrArg (fun z : Sˣ ↦ (↑z⁻¹ : S)) (initialTangentUnit_map W ha f)
  change f (↑(zeroInitialTangentUnit W ha)⁻¹ : R) =
    (↑(zeroInitialTangentUnit (W.map f) (ha.map f))⁻¹ : S) at hi
  rw [show F (algebraMap R R[T;T⁻¹] (↑(zeroInitialTangentUnit W ha)⁻¹ : R)) =
      algebraMap S S[T;T⁻¹] (↑(zeroInitialTangentUnit (W.map f) (ha.map f))⁻¹ : S) by
        change F (LaurentPolynomial.C _) = LaurentPolynomial.C _
        rw [PolygonScalingNaturality.coeffMap_C, hi]]
  rw [PolygonScalingNaturality.coeffMap_T_neg_one,
    laurentOppositeFactor_coefficient f W s b3 b4 b6 I J hf hI hJ ha hs h2 h3 h4 h6]

/-- The whole forward Laurent automorphism commutes with the original coefficient map. -/
theorem factorRatioLaurentEquiv_coefficient :
    (F).comp (e).toRingHom = (e').toRingHom.comp F := by
  have hu := factorRatioLaurentUnit_coefficient f W ha s
    b3 b4 b6 I J hf hI hJ hs h2 h3 h4 h6
  apply PolygonScalingNaturality.ringHom_ext
  · intro r
    change F (LaurentUnitPoints.evalUnit u (LaurentPolynomial.C r)) =
      LaurentUnitPoints.evalUnit u' (F (LaurentPolynomial.C r))
    simp only [LaurentUnitPoints.evalUnit_C, PolygonScalingNaturality.coeffMap_C]
    exact PolygonScalingNaturality.coeffMap_C f r
  · change F (LaurentUnitPoints.evalUnit u (LaurentPolynomial.T 1)) =
      LaurentUnitPoints.evalUnit u' (F (LaurentPolynomial.T 1))
    simp only [LaurentUnitPoints.evalUnit_T, zpow_one,
      PolygonScalingNaturality.coeffMap_T_one]
    exact congrArg Units.val hu
  · change F (LaurentUnitPoints.evalUnit u (LaurentPolynomial.T (-1))) =
      LaurentUnitPoints.evalUnit u' (F (LaurentPolynomial.T (-1)))
    simp only [LaurentUnitPoints.evalUnit_T, zpow_neg_one,
      PolygonScalingNaturality.coeffMap_T_neg_one]
    exact congrArg (fun z : S[T;T⁻¹]ˣ ↦ (↑z⁻¹ : S[T;T⁻¹])) hu

/-- The constructed inverse reparametrization also follows the actual coefficient restriction. -/
theorem factorRatioLaurentEquiv_symm_coefficient (x : R[T;T⁻¹]) :
    F ((e).symm x) = (e').symm (F x) := by
  apply (e').injective
  rw [AlgEquiv.apply_symm_apply]
  have h := congrArg (fun g : R[T;T⁻¹] →+* S[T;T⁻¹] ↦ g ((e).symm x))
    (factorRatioLaurentEquiv_coefficient f W ha s
      b3 b4 b6 I J hf hI hJ hs h2 h3 h4 h6)
  change F (e ((e).symm x)) = e' (F ((e).symm x)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

end FLT.Mazur.WeierstrassModificationX
