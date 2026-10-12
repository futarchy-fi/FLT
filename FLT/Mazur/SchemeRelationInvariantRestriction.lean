/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationDoubleRestriction
public import FLT.Mazur.RelativeRelationInvariantGlobalSections

/-!
# Full relation functions on an invariant open

On an invariant source open the full double restriction gives exactly the original
restricted endpoint equation. The comparison is the identity on regular functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationRestriction
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A X : Scheme.{u}} (p q : A ⟶ X) (W : X.Opens)
  (hW : p ⁻¹ᵁ W = q ⁻¹ᵁ W)

/-- Recover the original invariant relation domain from a full double-restriction arrow. -/
def toInvariantDomain : doubleDomain p q W.ι ⟶ (p ⁻¹ᵁ W).toScheme :=
  (isPullback_morphismRestrict p W).lift (fst p q W.ι) (arrow p q W.ι)
    (arrow_fst p q W.ι).symm

@[reassoc]
theorem toInvariantDomain_arrow : toInvariantDomain p q W ≫ (p ⁻¹ᵁ W).ι =
    arrow p q W.ι := (isPullback_morphismRestrict p W).lift_snd _ _ _

@[reassoc]
theorem toInvariantDomain_fst : toInvariantDomain p q W ≫ (p.resLE W (p ⁻¹ᵁ W) le_rfl) =
    fst p q W.ι := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (isPullback_morphismRestrict p W).lift_fst _ _ _

@[reassoc]
theorem toInvariantDomain_snd : toInvariantDomain p q W ≫ (q.resLE W (p ⁻¹ᵁ W) hW.le) =
    snd p q W.ι := by
  apply (cancel_mono W.ι).mp
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, toInvariantDomain_arrow_assoc, arrow_snd]

/-- The double restriction and the original invariant-domain equation test the same functions. -/
theorem invariant_compatible_iff (v : Γ(W.toScheme, ⊤)) :
    v ∈ compatibleFunctions (fst p q W.ι) (snd p q W.ι) ↔
      v ∈ compatibleFunctions (p.resLE W (p ⁻¹ᵁ W) le_rfl) (q.resLE W (p ⁻¹ᵁ W) hW.le) := by
  constructor
  · intro hv
    exact compatible_on_arrow p q W.ι (p ⁻¹ᵁ W).ι
      (p.resLE W (p ⁻¹ᵁ W) le_rfl) (q.resLE W (p ⁻¹ᵁ W) hW.le)
      (Scheme.Hom.resLE_comp_ι p le_rfl).symm
      (Scheme.Hom.resLE_comp_ι q hW.le).symm ⟨v, hv⟩
  · intro hv
    have h := congrArg (toInvariantDomain p q W).appTop hv
    change (toInvariantDomain p q W ≫ (p.resLE W (p ⁻¹ᵁ W) le_rfl)).appTop v =
      (toInvariantDomain p q W ≫ (q.resLE W (p ⁻¹ᵁ W) hW.le)).appTop v at h
    change (fst p q W.ι).appTop v = (snd p q W.ι).appTop v
    simpa only [toInvariantDomain_fst, toInvariantDomain_snd p q W hW] using h

/-- The full-relation function ring on an invariant open is the original endpoint equalizer. -/
def invariantFunctionEquiv :
    compatibleFunctions (p.resLE W (p ⁻¹ᵁ W) le_rfl) (q.resLE W (p ⁻¹ᵁ W) hW.le) ≃+*
    compatibleFunctions (fst p q W.ι) (snd p q W.ι) :=
  RingEquiv.subringCongr (SetLike.ext fun v ↦ (invariant_compatible_iff p q W hW v).symm)

/-- This equivalence retains the original function without any scalar-coordinate change. -/
theorem invariantFunctionEquiv_val
    (v : compatibleFunctions (p.resLE W (p ⁻¹ᵁ W) le_rfl)
      (q.resLE W (p ⁻¹ᵁ W) hW.le)) :
    (invariantFunctionEquiv p q W hW v).val = v.val := rfl

end FLT.Mazur.SchemeRelationRestriction
