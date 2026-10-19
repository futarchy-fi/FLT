/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteQuotientStages

/-!
# Transitions between the full complete-orbit quotient stages

The original quotient powers form an actual tower of closed immersions.
Their frame covers carry compatible transitions, retaining the original
frame inclusion and moving action at every order.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)
  (U : (source p q I o).Opens)
  (hU : ∀ g : Equiv.Perm I, (action e I o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
local notation "ρ" => restrictedAction (action e I o) U hU
local notation "J" => completeAffineOrbitIdeal e I o U hU

/-- Actual quotient reduction, with the full positive ideal powers. -/
def completeQuotientStageTransition {m n : ℕ} (h : m ≤ n) :
    completeQuotientStage e I o U hU m ⟶ completeQuotientStage e I o U hU n :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := J) (Nat.add_le_add_right h 1))))

instance completeQuotientStageTransition_closed {m n : ℕ} (h : m ≤ n) :
    IsClosedImmersion (completeQuotientStageTransition e I o U hU h) :=
  IsClosedImmersion.spec_of_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))

/-- The original quotient embedding is unchanged by transition. -/
@[reassoc] theorem completeQuotientStageTransition_map {m n : ℕ} (h : m ≤ n) :
    completeQuotientStageTransition e I o U hU h ≫ completeQuotientStageMap e I o U hU n =
      completeQuotientStageMap e I o U hU m := by
  unfold completeQuotientStageTransition completeQuotientStageMap
  rw [← Spec.map_comp]
  rfl

/-- Pull back quotient reduction to the actual original frame covers. -/
def completeQuotientFrameTransition {m n : ℕ} (h : m ≤ n) :
    completeQuotientFrame e I o U hU m ⟶ completeQuotientFrame e I o U hU n :=
  pullback.lift (pullback.fst (quotientMap ρ) (completeQuotientStageMap e I o U hU m))
    (completeQuotientFrameCover e I o U hU m ≫ completeQuotientStageTransition e I o U hU h)
    (by rw [Category.assoc, completeQuotientStageTransition_map]; exact pullback.condition)

/-- Transition retains the original ambient chart coordinate. -/
@[reassoc] theorem completeQuotientFrameTransition_fst {m n : ℕ} (h : m ≤ n) :
    completeQuotientFrameTransition e I o U hU h ≫
      pullback.fst (quotientMap ρ) (completeQuotientStageMap e I o U hU n) =
        pullback.fst (quotientMap ρ) (completeQuotientStageMap e I o U hU m) :=
  pullback.lift_fst _ _ _

/-- Transition covers precisely the quotient reduction. -/
@[reassoc] theorem completeQuotientFrameTransition_cover {m n : ℕ} (h : m ≤ n) :
    completeQuotientFrameTransition e I o U hU h ≫
      completeQuotientFrameCover e I o U hU n =
        completeQuotientFrameCover e I o U hU m ≫
          completeQuotientStageTransition e I o U hU h := pullback.lift_snd _ _ _

/-- Every transition preserves the unchanged original normalized frame. -/
@[reassoc] theorem completeQuotientFrameTransition_inclusion {m n : ℕ} (h : m ≤ n) :
    completeQuotientFrameTransition e I o U hU h ≫
      completeQuotientFrameInclusion e I o U hU n =
        completeQuotientFrameInclusion e I o U hU m := by
  unfold completeQuotientFrameInclusion
  rw [completeQuotientFrameTransition_fst_assoc]

/-- Composition is exact on the full nonreduced covers. -/
@[reassoc] theorem completeQuotientFrameTransition_comp {l m n : ℕ}
    (h : l ≤ m) (h' : m ≤ n) :
    completeQuotientFrameTransition e I o U hU h ≫
      completeQuotientFrameTransition e I o U hU h' =
        completeQuotientFrameTransition e I o U hU (h.trans h') := by
  apply (cancel_mono (completeQuotientFrameInclusion e I o U hU n)).mp
  rw [Category.assoc, completeQuotientFrameTransition_inclusion,
    completeQuotientFrameTransition_inclusion, completeQuotientFrameTransition_inclusion]

/-- At equal orders, the transition is the identity. -/
theorem completeQuotientFrameTransition_refl (n : ℕ) :
    completeQuotientFrameTransition e I o U hU (le_refl n) = 𝟙 _ := by
  apply (cancel_mono (completeQuotientFrameInclusion e I o U hU n)).mp
  rw [completeQuotientFrameTransition_inclusion, Category.id_comp]

/-- The original moving action commutes with every order transition. -/
@[reassoc] theorem completeQuotientFrameTransition_equivariant {m n : ℕ} (h : m ≤ n)
    (g : Equiv.Perm I) :
    (completeQuotientFrameAction e I o U hU m g).hom ≫
      completeQuotientFrameTransition e I o U hU h =
        completeQuotientFrameTransition e I o U hU h ≫
          (completeQuotientFrameAction e I o U hU n g).hom := by
  apply (cancel_mono (completeQuotientFrameInclusion e I o U hU n)).mp
  rw [Category.assoc, completeQuotientFrameTransition_inclusion,
    completeQuotientFrameAction_inclusion, Category.assoc,
    completeQuotientFrameAction_inclusion, completeQuotientFrameTransition_inclusion_assoc]

end FLT.Mazur.EquivalenceRelationNormalizedFrames
