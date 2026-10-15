/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationRestrictionRechart
public import FLT.Mazur.SchemeOpenSectionDescent

/-!
# Full relation functions descend through a covering source refinement

A source cover preserves the compatible-function ring of the full original
relation. Both endpoints lift independently; no monicity or equality of ground
coordinates is imposed on the covering map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationRestriction
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A X Y Z : Scheme.{u}} (p q : A ⟶ X)

/-- A full double restriction of a covering source still covers the original arrows. -/
instance arrow_surjective (k : Y ⟶ X) [Surjective k] : Surjective (arrow p q k) := by
  unfold arrow
  infer_instance

instance arrow_flat (k : Y ⟶ X) [Flat k] : Flat (arrow p q k) := by
  unfold arrow
  infer_instance

instance arrow_locallyOfFinitePresentation (k : Y ⟶ X) [LocallyOfFinitePresentation k] :
    LocallyOfFinitePresentation (arrow p q k) := by
  unfold arrow
  infer_instance

variable (r : X ⟶ A) (hrp : r ≫ p = 𝟙 X) (hrq : r ≫ q = 𝟙 X)
  (k : Y ⟶ X) (l : Z ⟶ X) (h : Y ⟶ Z) (hk : h ≫ l = k)
  [Flat h] [LocallyOfFinitePresentation h] [Surjective h]

omit [Flat h] [LocallyOfFinitePresentation h] [Surjective h] in
include hrp hrq hk in
/-- Full original compatibility implies the source cover's actual kernel-pair equation. -/
theorem sourceCover_kernel (v : compatibleFunctions (fst p q k) (snd p q k)) :
    (pullback.fst h h).appTop v.val = (pullback.snd h h).appTop v.val := by
  apply compatible_on_arrow p q k (pullback.fst h h ≫ k ≫ r)
  · rw [Category.assoc, Category.assoc, hrp, Category.comp_id]
  · rw [Category.assoc, Category.assoc, hrq, Category.comp_id,
      ← hk, ← Category.assoc, pullback.condition, Category.assoc]

include hk in
/-- Independent lifts of both endpoints detect invariance after source descent. -/
theorem sourceCover_invariant (v : compatibleFunctions (fst p q k) (snd p q k))
    (t : Γ(Z, ⊤)) (ht : h.appTop t = v.val) :
    t ∈ compatibleFunctions (fst p q l) (snd p q l) := by
  let a := arrow (fst p q l) (snd p q l) h
  apply appTop_injective a
  change (a ≫ fst p q l).appTop t = (a ≫ snd p q l).appTop t
  rw [arrow_fst, arrow_snd]
  change (fst (fst p q l) (snd p q l) h).appTop (h.appTop t) =
    (snd (fst p q l) (snd p q l) h).appTop (h.appTop t)
  rw [ht]
  apply compatible_on_arrow p q k (a ≫ arrow p q l)
  · rw [Category.assoc, arrow_fst, ← Category.assoc, arrow_fst, Category.assoc, hk]
  · rw [Category.assoc, arrow_snd, ← Category.assoc, arrow_snd, Category.assoc, hk]

include hrp hrq hk in
/-- Every full compatible function descends uniquely through the source cover. -/
theorem sourceCover_existsUnique (v : compatibleFunctions (fst p q k) (snd p q k)) :
    ∃! t : compatibleFunctions (fst p q l) (snd p q l), h.appTop t.val = v.val := by
  obtain ⟨t, ht, _⟩ := sections_existsUnique (IsPullback.of_hasPullback h h) v.val
    (sourceCover_kernel p q r hrp hrq k l h hk v)
  exact ⟨⟨t, sourceCover_invariant p q k l h hk v t ht⟩, ht,
    fun w hw ↦ Subtype.ext (appTop_injective h (hw.trans ht.symm))⟩

/-- The original geometric pullback is an equivalence of the full invariant rings. -/
def sourceCoverEquiv : compatibleFunctions (fst p q l) (snd p q l) ≃+*
    compatibleFunctions (fst p q k) (snd p q k) := by
  apply RingEquiv.ofBijective (sourcePullback p q k l h hk)
  constructor
  · intro v w hvw
    exact Subtype.ext (appTop_injective h (congrArg Subtype.val hvw))
  · intro v
    obtain ⟨t, ht, _⟩ := sourceCover_existsUnique p q r hrp hrq k l h hk v
    exact ⟨t, Subtype.ext ht⟩

/-- The equivalence preserves the entire original regular function. -/
theorem sourceCoverEquiv_val (v : compatibleFunctions (fst p q l) (snd p q l)) :
    (sourceCoverEquiv p q r hrp hrq k l h hk v).val = h.appTop v.val := rfl

end FLT.Mazur.SchemeRelationRestriction
