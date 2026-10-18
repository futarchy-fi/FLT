/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLaurentEquiv
public import FLT.Mazur.WeierstrassInfinityFactorRatioCongruence
public import FLT.Mazur.NilpotentAlgebraEquivalence

/-!
# The entire original infinity factor ratio is an isomorphism

The regular ratio is a nilpotent perturbation of the reciprocal tangent
equivalence. Finite correction constructs its inverse at every arithmetic order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)
  (s b3 : R) (r : Polynomial R) (hr : r ∈ I.map Polynomial.C) (hb : b3 ∈ I)
local notation "B" => Coordinate W 1
local notation "a" => infinityFactorRatioUnit W I hI h2 h3 h4 h6 s b3 r hr hb
local notation "E" => nilpotentInfinityChartLaurentEquiv W ha I hI h2 h3 h4 h6
local notation "P" => infinityFactorRatioParameter W I hI h2 h3 h4 h6 s b3 r hr hb

include ha in
/-- Evaluation at the full original regular ratio is bijective on the entire Laurent algebra. -/
theorem infinityFactorRatioEvaluation_bijective :
    Function.Bijective (LaurentUnitPoints.evalUnit (R := R) a) := by
  apply NilpotentAlgebraEquivalence.bijective I hI
    (LaurentPolynomial.invert.trans (E).symm)
  refine LaurentNilpotentReparametrization.hom_sub_mem _ _
    (LaurentPolynomial.invert.trans (E).symm).toAlgHom ?_
  simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply, LaurentPolynomial.invert_T]
  change LaurentUnitPoints.evalUnit (R := R) a (LaurentPolynomial.T 1) -
    nilpotentInfinityLaurentToChart W I hI h2 h3 h4 h6 (LaurentPolynomial.T (-1)) ∈
      I.map (algebraMap R B)
  simpa only [LaurentUnitPoints.evalUnit_T, zpow_one, zpow_neg_one,
    nilpotentInfinityLaurentToChart] using
      infinityFactorRatioUnit_sub_inverse_tangent_mem W I hI h2 h3 h4 h6 s b3 r hr hb

/-- The full factor-ratio algebra equivalence, with inverse supplied by finite correction. -/
def infinityFactorRatioEquiv : R[T;T⁻¹] ≃ₐ[R] B :=
  AlgEquiv.ofBijective (LaurentUnitPoints.evalUnit a)
    (infinityFactorRatioEvaluation_bijective W ha I hI h2 h3 h4 h6 s b3 r hr hb)

/-- The equivalence preserves the exact original factor-ratio map. -/
theorem infinityFactorRatioEquiv_toAlgHom :
    (infinityFactorRatioEquiv W ha I hI h2 h3 h4 h6 s b3 r hr hb).toAlgHom =
      LaurentUnitPoints.evalUnit a := rfl

/-- The complete original infinity chart is the torus, using its actual regular ratio. -/
def infinityFactorRatioIso : Spec (.of B) ≅ Spec (.of R[T;T⁻¹]) :=
  Scheme.Spec.mapIso
    (infinityFactorRatioEquiv W ha I hI h2 h3 h4 h6 s b3 r hr hb).toRingEquiv.toCommRingCatIso.op

/-- The constructed isomorphism is precisely the previously defined full parameter. -/
theorem infinityFactorRatioIso_hom :
    (infinityFactorRatioIso W ha I hI h2 h3 h4 h6 s b3 r hr hb).hom = P := rfl

include ha in
/-- Nilpotence suffices for the original parameter to be an isomorphism. -/
theorem infinityFactorRatioParameter_isIso : IsIso P := by
  rw [← infinityFactorRatioIso_hom W ha]
  infer_instance

include ha in
/-- The full original infinity parameter reaches every torus point at every order. -/
theorem infinityFactorRatioParameter_surjective : Function.Surjective P := by
  rw [← infinityFactorRatioIso_hom W ha]
  exact (Scheme.homeoOfIso (infinityFactorRatioIso W ha I hI h2 h3 h4 h6 s b3 r hr hb)).surjective

end FLT.Mazur.WeierstrassIntegralChart
