/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedFrames
public import FLT.Mazur.RelativeDistinctEtale
public import FLT.Mazur.UnramifiedSectionImmersion

/-!
# Normalized frames as a pullback of the original identity section

The normalized equalizer is the inverse image of the original reflexive section
under its distinguished full relation coordinate. Thus its inclusion is open
when the original first projection is etale, and its first projection is etale.
No completeness neighborhood is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o : I)

local instance normalizedEtaleOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›

/-- Normalization is the actual pullback of the original reflexive relation section. -/
theorem identity_isPullback : IsPullback (inclusion p q I o) (first p q I o)
    (distinctCoordinate (Over.mk p) I o).left e.r := by
  apply IsPullback.of_isLimit
    (c := PullbackCone.mk (inclusion p q I o) (first p q I o)
      (distinguished_eq_identity p q I o e))
  refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
  · intro s
    apply equalizer.lift s.fst
    have hb : s.fst ≫ (distinctScheme (Over.mk p) I).hom = s.snd := by
      calc
        _ = s.fst ≫ (distinctCoordinate (Over.mk p) I o).left ≫ p := by
          exact congrArg (fun z ↦ s.fst ≫ z)
            (distinctCoordinate (Over.mk p) I o).w.symm
        _ = s.snd ≫ e.r ≫ p := by rw [← Category.assoc, s.condition, Category.assoc]
        _ = s.snd := by rw [e.reflexivity₁, Category.comp_id]
    rw [hb, ← Category.assoc, s.condition, Category.assoc,
      e.reflexivity₂, Category.comp_id]
  · intro s
    exact equalizer.lift_ι _ _
  · intro s
    change (equalizer.lift s.fst _) ≫ inclusion p q I o ≫ _ = s.snd
    rw [← Category.assoc, show equalizer.lift s.fst _ ≫ inclusion p q I o = s.fst
      from equalizer.lift_ι _ _]
    calc
      _ = s.fst ≫ (distinctCoordinate (Over.mk p) I o).left ≫ p := by
        exact congrArg (fun z ↦ s.fst ≫ z)
            (distinctCoordinate (Over.mk p) I o).w.symm
      _ = s.snd ≫ e.r ≫ p := by rw [← Category.assoc, s.condition, Category.assoc]
      _ = s.snd := by rw [e.reflexivity₁, Category.comp_id]
  · intro s m hm _
    apply (cancel_mono (inclusion p q I o)).mp
    exact hm.trans (equalizer.lift_ι _ _).symm

variable [Etale p]

local instance normalizedEtaleOver_etale : Etale (Over.mk p).hom := ‹Etale p›

include e in
/-- The normalized source is an open subscheme of the entire distinct frame scheme. -/
theorem inclusion_isOpenImmersion : IsOpenImmersion (inclusion p q I o) := by
  let _ := UnramifiedSectionImmersion.isOpenImmersion p e.r e.reflexivity₁
  exact IsOpenImmersion.of_isPullback (identity_isPullback e I o).flip inferInstance

include e in
/-- The normalized frame source is etale over its original first endpoint. -/
theorem first_etale : Etale (first p q I o) := by
  let _ := inclusion_isOpenImmersion e I o
  change Etale (inclusion p q I o ≫ (distinctScheme (Over.mk p) I).hom)
  infer_instance

end FLT.Mazur.EquivalenceRelationNormalizedFrames
