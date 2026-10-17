/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticHigherRebaseIdentification
public import FLT.Mazur.PolygonArithmeticCorrectionPunctures
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Full two-branch puncture identification at any square-zero layer

A positive integral field on each branch determines both complete Laurent
substitutions of the lifted node. The input smoothing remains arbitrary,
subject only to the layer parameter annihilating it.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R) (m r : ℕ)
local notation "Q" => Quotient R π m
local notation "e" => parameter R π m ^ (r + 1)

/-- A boundary-vanishing integral field remains its own positive part after specialization. -/
theorem correctionField_positive_of_boundary (q : R[T;T⁻¹])
    (hq : ∀ d : ℤ, d ≤ 0 → q.coeff d = 0) :
    positivePart (correctionField R π m q) = correctionField R π m q := by
  ext d
  rw [positivePart_coeff]
  split_ifs with hd
  · rfl
  · exact (correctionField_boundary R π m q hq d (by omega)).symm

/-- Both whole punctures equal their specified higher-order square-zero substitutions. -/
theorem twoBranchCorrectionPunctureFactor_higher_eq (he : e ^ 2 = 0)
    (t : Q) (ht : e * t = 0) (q : Bool → R[T;T⁻¹])
    (hq : ∀ b d, d ≤ 0 → (q b).coeff d = 0) (b : Bool) :
    twoBranchCorrectionPunctureFactor R π m t
        (fun a ↦ higherCorrectionField R π r (q a)) b =
      LaurentSquareZeroAutomorphism.equiv e he (correctionField R π m (q b)) := by
  let p := fun a ↦ correctionField R π m (q a)
  have hp : ∀ a, positivePart (p a) = p a :=
    fun a ↦ correctionField_positive_of_boundary R π m (q a) (hq a)
  apply punctureFactor_source_identification _ t
    (twoBranchCorrectionSmoothing_higher_eq R π m r t ht q)
    (twoBranchCorrectionNodeFactor R π m t (fun a ↦ higherCorrectionField R π r (q a)))
    (squareZeroTwoBranchFactor t e he ht p) _ _ b
    (twoBranchCorrectionNodeFactor_higher_eq R π m r he t ht q p (fun a ↦ (hp a).symm))
    (twoBranchCorrectionNodeFactor_puncture R π m t _ b)
  have h := squareZeroTwoBranchFactor_boundary t e he ht p b
  rw [hp] at h
  cases b <;> exact h

/-- The terminal rebase retains both complete positive higher-layer substitutions. -/
theorem twoBranchCorrectionRebasedPunctureFactor_higher_eq (he : e ^ 2 = 0)
    (t : Q) (ht : e * t = 0) (q : Bool → R[T;T⁻¹])
    (hq : ∀ b d, d ≤ 0 → (q b).coeff d = 0) (b : Bool) :
    twoBranchCorrectionRebasedPunctureFactor R π m t
        (fun a ↦ higherCorrectionField R π r (q a)) b =
      LaurentSquareZeroAutomorphism.equiv e he (correctionField R π m (q b)) := by
  let p := fun a ↦ correctionField R π m (q a)
  have hp : ∀ a, positivePart (p a) = p a :=
    fun a ↦ correctionField_positive_of_boundary R π m (q a) (hq a)
  apply punctureFactor_rebased_identification _ t
    (twoBranchCorrectionRebasedSmoothing_higher_eq R π m r t ht q)
    (twoBranchCorrectionRebasedFactor R π m t (fun a ↦ higherCorrectionField R π r (q a)))
    (squareZeroTwoBranchFactor t e he ht p) _ _ b
    (twoBranchCorrectionRebasedFactor_higher_eq R π m r he t ht q p
      (fun a ↦ (hp a).symm))
    (twoBranchCorrectionRebasedFactor_puncture R π m t _ b)
  have h := squareZeroTwoBranchFactor_boundary t e he ht p b
  rw [hp] at h
  cases b <;> exact h

end FLT.Mazur.PolygonArithmeticStages
