/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanRestrictionCoordinates

/-!
# Actual finite restrictions into one overlap chart

Starting only with the original principal coordinate isomorphisms, construct
all incoming finite restrictions into a later double-open target. The old
source overlap rings and the full ambient chart equations are retained.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v} [Finite ι]
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)] {a : ι → A} {b : ∀ i, B i}
  (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away (b i))

/-- Construct finite restrictions, with one enlarged target stage and fixed source overlaps. -/
theorem exists_principalFan_finite_restrictions
    (x : PrincipalFanStage a b (fun i ↦ (e i).toAlgHom)) (j : ι)
    (t : Set.Ici (x.target j)) :
    ∃ (q : Set.Ici (x.target j)) (_htq : t ≤ q),
      ∃ ρ : ∀ i, PrincipalStage R (B i) (b i) (x.target i) →ₐ[R]
        FiniteRelationIterated.Stage R (relationIdeal R (B j))
          (principalRepresentative R (B j) (b j)) (x.target j)
          (principalFanRestrictionDenominator x i j) q,
        ∀ i, (ρ i).comp (principalFanAmbient x i) =
          (Algebra.algHom R (PrincipalStage R (B j) (b j) q.val)
            (FiniteRelationIterated.Stage R (relationIdeal R (B j))
              (principalRepresentative R (B j) (b j)) (x.target j)
              (principalFanRestrictionDenominator x i j) q)).comp
            ((principalTransition (b j) q.property).comp (principalFanAmbient x j)) := by
  let b' := (principalTransition (b j) t.property).comp (principalFanAmbient x j)
  have hb : (FiniteRelationLocalization.toQuotient R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) t.val).comp b' =
      (principalFanOriginalAmbient (f := fun i ↦ (e i).toAlgHom) j).comp
        (stageMap R A x.source) := by
    dsimp only [b']
    rw [← AlgHom.comp_assoc]
    exact (congrArg (fun h ↦ h.comp (principalFanAmbient x j))
      (FiniteRelationLocalization.toQuotient_comp R (relationIdeal R (B j))
        (principalRepresentative R (B j) (b j)) t.property)).trans
          (principalFanAmbient_quotient x j)
  obtain ⟨q, htq, ρ, hρ⟩ := FiniteRelationIterated.exists_restrictions_of_coordinates
    (relationIdeal R (B j)) (principalRepresentative R (B j) (b j)) (x.target j)
    (fun i ↦ principalFanRestrictionDenominator x i j)
    (fun _ ↦ A) (fun i ↦ Localization.Away (b i)) a e
    (fun _ ↦ principalFanOriginalAmbient (f := fun i ↦ (e i).toAlgHom) j)
    (fun i ↦ principalFanRestrictionDenominator_spec x i j)
    (fun i ↦ PrincipalStage R (B i) (b i) (x.target i))
    (fun _ ↦ Stage R A x.source) t (fun _ ↦ stageMap R A x.source)
    (fun i ↦ principalStageMap R (B i) (b i) (x.target i))
    (principalFanAmbient x) (fun _ ↦ b') (principalFanAmbient_fac x) (fun _ ↦ hb)
  refine ⟨q, htq, ρ, fun i ↦ ?_⟩
  rw [hρ]
  congr 1
  exact (AlgHom.comp_assoc _ _ _).symm.trans
    (congrArg (fun h ↦ h.comp (principalFanAmbient x j))
      (principalTransition_comp (b j) t.property htq))

end FLT.Mazur.FiniteTypeRelationModel
