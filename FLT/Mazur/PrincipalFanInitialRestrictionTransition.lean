/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanInitialRestriction
public import FLT.Mazur.PrincipalOccurrenceRefinedPaths

/-!
# Transport canonical restrictions to a later literal target

The simultaneous polynomial refinement API starts an iterated localization
at its own relation stage. Its reflexive denominator transition gives the
canonical fan restriction ring, and the comparison preserves projection.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)] {a : ι → A} {b : ∀ i, B i}
  (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away (b i))


variable {x y : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)}

/-- Send the canonical old double open to the literal later double open. -/
def principalFanInitialRestrictionTransition (h : x ≤ y) (i j : ι) :
    PrincipalFanRestrictionTarget x i j →ₐ[R] PrincipalFanOldRestrictionTarget h i j :=
  (FiniteRelationIterated.transition R (relationIdeal R (B j))
    (principalRepresentative R (B j) (b j)) (x.target j)
    (principalFanRestrictionDenominator x i j)
    (show (⟨x.target j, le_refl (x.target j)⟩ : Set.Ici (x.target j)) ≤
      ⟨y.target j, principalFan_target_mono h j⟩ from principalFan_target_mono h j)).comp
      (principalFanInitialRestrictionEquiv e x i j).toAlgHom

/-- Canonical numerators become the transitioned numerators in the literal later target. -/
theorem principalFanInitialRestrictionTransition_algebraMap (h : x ≤ y) (i j : ι)
    (z : PrincipalStage R (B j) (b j) (x.target j)) :
    principalFanInitialRestrictionTransition e h i j (algebraMap _ _ z) =
      algebraMap _ (PrincipalFanOldRestrictionTarget h i j)
        (principalTransition (b j) (principalFan_target_mono h j) z) := by
  change FiniteRelationIterated.transition R _ _ _ _ _
    (principalFanInitialRestrictionEquiv e x i j (algebraMap _ _ z)) = _
  rw [principalFanInitialRestrictionEquiv_algebraMap,
    FiniteRelationIterated.transition_algebraMap]

end FLT.Mazur.FiniteTypeRelationModel
