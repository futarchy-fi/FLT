/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationDoubleRestriction

/-!
# Changing coordinates on a full relation restriction

Source maps induce pullbacks on compatible functions for the full relation.
A source isomorphism over the original scheme gives a ring equivalence through
the actual pullback, without dropping any original relation arrows.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationRestriction
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {A X Y Z : Scheme.{u}} (p q : A ⟶ X) (k : Y ⟶ X) (l : Z ⟶ X)
  (h : Y ⟶ Z) (hk : h ≫ l = k)

include hk in
/-- Actual source pullback preserves full two-endpoint compatibility. -/
theorem sourcePullback_mem (v : compatibleFunctions (fst p q l) (snd p q l)) :
    h.appTop v.val ∈ compatibleFunctions (fst p q k) (snd p q k) := by
  change (fst p q k ≫ h).appTop v.val = (snd p q k ≫ h).appTop v.val
  apply compatible_on_arrow p q l (arrow p q k) (fst p q k ≫ h) (snd p q k ≫ h)
  · rw [Category.assoc, hk, arrow_fst]
  · rw [Category.assoc, hk, arrow_snd]

/-- The full-relation function pullback is the unchanged geometric pullback. -/
def sourcePullback : compatibleFunctions (fst p q l) (snd p q l) →+*
    compatibleFunctions (fst p q k) (snd p q k) :=
  (h.appTop.hom.comp (compatibleFunctions (fst p q l) (snd p q l)).subtype).codRestrict
    _ (sourcePullback_mem p q k l h hk)

/-- The source isomorphism identifies the full original compatible-function rings. -/
def sourceIsoEquiv (i : Y ≅ Z) (hi : i.hom ≫ l = k) :
    compatibleFunctions (fst p q l) (snd p q l) ≃+*
      compatibleFunctions (fst p q k) (snd p q k) := by
  apply RingEquiv.ofBijective (sourcePullback p q k l i.hom hi)
  constructor
  · intro v w hvw
    exact Subtype.ext (appTop_injective i.hom (congrArg Subtype.val hvw))
  · intro v
    have hinv : i.inv ≫ k = l := by rw [← hi, Iso.inv_hom_id_assoc]
    refine ⟨sourcePullback p q l k i.inv hinv v, Subtype.ext ?_⟩
    change (i.hom ≫ i.inv).appTop v.val = v.val
    rw [Iso.hom_inv_id]
    rfl

/-- The coordinate equivalence is actual pullback on regular functions. -/
theorem sourceIsoEquiv_val (i : Y ≅ Z) (hi : i.hom ≫ l = k)
    (v : compatibleFunctions (fst p q l) (snd p q l)) :
    (sourceIsoEquiv p q k l i hi v).val = i.hom.appTop v.val := rfl

end FLT.Mazur.SchemeRelationRestriction
