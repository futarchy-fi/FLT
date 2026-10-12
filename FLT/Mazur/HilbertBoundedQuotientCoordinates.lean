/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFamilyGrassmannianSchemeMap

/-!
# Original Hilbert quotient coordinates on the bounded ambient

A prescribed basis of the actual quotient gives an explicit normalized
bounded evaluation. Its kernel is the entire Grassmannian relation, and
its coefficients are the original polynomial quotient coordinates. These
are the local coordinate maps needed for the Hilbert immersion construction.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R S I : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (J : Ideal (MvPolynomial I S)) (d : ℕ)
  (v : Module.Basis (Fin d) S (MvPolynomial I S ⧸ J))

/-- Normalized bounded evaluation uses coordinates in the original polynomial quotient. -/
def hilbertAmbientCoordinates :
    (S ⊗[R] MvPolynomial.restrictTotalDegree I R (d + 1)) →ₗ[S] (Fin d → S) :=
  v.equivFun.toLinearMap.comp ((boundedQuotientEvaluation S I J (d + 1)).comp
    (boundedPolynomialBaseChangeEquiv R S I (d + 1)).toLinearMap)

/-- Pure-tensor coordinates are the actual polynomial evaluations with their scalar factors. -/
theorem hilbertAmbientCoordinates_tmul (s : S)
    (p : MvPolynomial.restrictTotalDegree I R (d + 1)) :
    hilbertAmbientCoordinates R S I J d v (s ⊗ₜ[R] p) =
      s • v.equivFun (Ideal.Quotient.mk J (MvPolynomial.map (algebraMap R S) p.val)) := by
  change v.equivFun (Ideal.Quotient.mk J
    (boundedPolynomialBaseChangeEquiv R S I (d + 1) (s ⊗ₜ[R] p)).val) = _
  rw [boundedPolynomialBaseChangeEquiv_tmul]
  change v.equivFun ((Ideal.Quotient.mkₐ S J)
    (s • MvPolynomial.map (algebraMap R S) p.val)) = _
  rw [map_smul, map_smul]
  rfl

/-- Each bounded monomial column is its actual coordinate vector in the full quotient. -/
theorem hilbertAmbientCoordinates_monomial (m : BoundedHilbertMonomials I (d + 1)) :
    hilbertAmbientCoordinates R S I J d v
        (1 ⊗ₜ[R] boundedPolynomialBasis R I (d + 1) m) =
      v.equivFun (Ideal.Quotient.mk J (MvPolynomial.monomial m.val 1)) := by
  rw [hilbertAmbientCoordinates_tmul, one_smul, boundedPolynomialBasis_val,
    MvPolynomial.map_monomial, map_one]

variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

/-- The normalized coordinate map has exactly the original Hilbert Grassmannian relation. -/
theorem hilbertAmbientCoordinates_kernel :
    (hilbertAmbientCoordinates R S I J d v).ker =
      (finiteFlatHilbertAmbientPoint R S I J d hd).toSubmodule := by
  ext x
  rw [finiteFlatHilbertAmbientPoint_mem]
  change v.equivFun (boundedQuotientEvaluation S I J (d + 1)
    (boundedPolynomialBaseChangeEquiv R S I (d + 1) x)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  rfl

include hd in
/-- Every original quotient coordinate is attained by bounded polynomial evaluation. -/
theorem hilbertAmbientCoordinates_surjective :
    Function.Surjective (hilbertAmbientCoordinates R S I J d v) :=
  v.equivFun.surjective.comp
    ((boundedQuotientEvaluation_surjective_of_le S I J d (d + 1) hd (Nat.le_succ d)).comp
      (boundedPolynomialBaseChangeEquiv R S I (d + 1)).surjective)

end FLT.Mazur.HilbertChart
