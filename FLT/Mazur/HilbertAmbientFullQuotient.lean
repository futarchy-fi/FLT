/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFamilyGrassmannianSchemeMap

/-!
# The original ambient quotient is the full polynomial quotient

Compose the two actual quotient comparisons. The resulting equivalence computes
on every ambient vector and, in particular, on each bounded monomial column.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R S I : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (J : Ideal (MvPolynomial I S)) (d : ℕ)
  [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
  [Module.Flat S (MvPolynomial I S ⧸ J)]
  (hd : ∀ p : PrimeSpectrum S, Module.finrank p.asIdeal.ResidueField
    (MvPolynomial I p.asIdeal.ResidueField ⧸
      J.map (MvPolynomial.map (algebraMap S p.asIdeal.ResidueField))) = d)

/-- Identify the entire original ambient quotient with the original polynomial quotient. -/
def hilbertAmbientFullQuotientEquiv :
    ((S ⊗[R] MvPolynomial.restrictTotalDegree I R (d + 1)) ⧸
      (finiteFlatHilbertAmbientPoint R S I J d hd).toSubmodule) ≃ₗ[S]
        (MvPolynomial I S ⧸ J) :=
  (ambientTransportQuotientEquiv (boundedPolynomialBaseChangeEquiv R S I (d + 1)).symm
    (finiteFlatGrassmannianParameter S I J d hd)).trans
      (boundedRelationQuotientEquiv S I J d (d + 1) hd (Nat.le_succ d))

/-- The comparison evaluates any original bounded ambient vector in the full quotient. -/
theorem hilbertAmbientFullQuotientEquiv_mkQ
    (x : S ⊗[R] MvPolynomial.restrictTotalDegree I R (d + 1)) :
    hilbertAmbientFullQuotientEquiv R S I J d hd
        ((finiteFlatHilbertAmbientPoint R S I J d hd).toSubmodule.mkQ x) =
      boundedQuotientEvaluation S I J (d + 1)
        (boundedPolynomialBaseChangeEquiv R S I (d + 1) x) := by
  change boundedRelationQuotientEquiv S I J d (d + 1) hd (Nat.le_succ d)
    (ambientTransportQuotientEquiv (boundedPolynomialBaseChangeEquiv R S I (d + 1)).symm
      (finiteFlatGrassmannianParameter S I J d hd) (Submodule.Quotient.mk x)) = _
  rw [ambientTransportQuotientEquiv, LinearMap.quotKerEquivOfSurjective_apply_mk]
  change boundedRelationQuotientEquiv S I J d (d + 1) hd (Nat.le_succ d)
    (Submodule.Quotient.mk (boundedPolynomialBaseChangeEquiv R S I (d + 1) x)) = _
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

/-- Every bounded monomial retains its actual class modulo the whole polynomial ideal. -/
theorem hilbertAmbientFullQuotientEquiv_monomial
    (m : BoundedHilbertMonomials I (d + 1)) :
    hilbertAmbientFullQuotientEquiv R S I J d hd
        ((finiteFlatHilbertAmbientPoint R S I J d hd).toSubmodule.mkQ
          (1 ⊗ₜ[R] boundedPolynomialBasis R I (d + 1) m)) =
      Ideal.Quotient.mk J (MvPolynomial.monomial m.val 1) := by
  rw [hilbertAmbientFullQuotientEquiv_mkQ, boundedPolynomialBaseChangeEquiv_basis]
  change Ideal.Quotient.mk J (boundedPolynomialBasis S I (d + 1) m).val = _
  rw [boundedPolynomialBasis_val]

attribute [irreducible] hilbertAmbientFullQuotientEquiv

end FLT.Mazur.HilbertChart
