/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupRefinementTransport

/-!
# Composition coherence for full compatible subgroup transport

Two changes of parameter presentation agree with the direct change, through
the canonical iterated pullback comparison. These are equalities of bundled
compatible isomorphisms, not just of their modular classes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U V : Scheme} {n : ℕ} {E : GeneralizedEllipticCurve S}

/-- A compatible isomorphism can be cancelled from the right. -/
theorem CompatibleIso.trans_right_cancel {D F G : GeneralizedEllipticCurve S}
    {A : D.FiniteSubgroup n} {B : F.FiniteSubgroup n} {C : G.FiniteSubgroup n}
    {a b : CompatibleIso A B} (c : CompatibleIso B C) (h : a.trans c = b.trans c) :
    a = b := by
  have h' := congrArg (fun z ↦ z.trans c.symm) h
  simpa only [CompatibleIso.trans_assoc, CompatibleIso.trans_symm,
    CompatibleIso.trans_refl] using h'

/-- Cancel an inverse comparison against the next factor without losing the final comparison. -/
theorem CompatibleIso.symm_trans_assoc {D F G : GeneralizedEllipticCurve S}
    {A : D.FiniteSubgroup n} {B : F.FiniteSubgroup n} {C : G.FiniteSubgroup n}
    (a : CompatibleIso A B) (b : CompatibleIso B C) : a.symm.trans (a.trans b) = b := by
  rw [← CompatibleIso.trans_assoc, CompatibleIso.symm_trans, CompatibleIso.refl_trans]

/-- Pullback preserves the inverse of a full compatible subgroup comparison. -/
theorem CompatibleIso.baseChange_symm {F : GeneralizedEllipticCurve S}
    {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}
    (a : CompatibleIso H J) (f : T ⟶ S) :
    a.symm.baseChange f = (a.baseChange f).symm := by
  apply CompatibleIso.ext_curve
  exact Functor.mapIso_symm (baseChangeFunctor f) a.curve

/-- The threefold comparison is coherent for arbitrary supplied composite equalities. -/
theorem compatibleBaseChangeCompEq_assoc (H : E.FiniteSubgroup n)
    (p : T ⟶ S) (q : U ⟶ S) (r : V ⟶ S) (f : U ⟶ T) (j : V ⟶ U)
    (w : q = f ≫ p) (v : r = j ≫ q) :
    (compatibleBaseChangeCompEq H p (j ≫ f) r (by rw [v, w, Category.assoc])).trans
      (compatibleBaseChangeComp (H.baseChange p) f j) =
    (compatibleBaseChangeCompEq H q j r v).trans
      ((compatibleBaseChangeCompEq H p f q w).baseChange j) := by
  subst q
  have hr : r = (j ≫ f) ≫ p := by rw [v, Category.assoc]
  subst r
  exact compatibleBaseChangeComp_assoc H p f j

/-- Full subgroup comparisons satisfy the refinement cocycle under composition. -/
theorem compatibleRefinementTransport_comp (H : E.FiniteSubgroup n)
    (p : T ⟶ S) (q : U ⟶ S) (r : V ⟶ S) (f : U ⟶ T) (j : V ⟶ U)
    (w : q = f ≫ p) (v : r = j ≫ q)
    {D : GeneralizedEllipticCurve T} {F : GeneralizedEllipticCurve U}
    {G : GeneralizedEllipticCurve V}
    {A : D.FiniteSubgroup n} {B : F.FiniteSubgroup n} {C : G.FiniteSubgroup n}
    (a : CompatibleIso A (H.baseChange p)) (b : CompatibleIso B (H.baseChange q))
    (c : CompatibleIso C (H.baseChange r)) :
    (compatibleRefinementTransport H q r j v b c).trans
      ((compatibleRefinementTransport H p q f w a b).baseChange j) =
    (compatibleRefinementTransport H p r (j ≫ f) (by rw [v, w, Category.assoc]) a c).trans
      (compatibleBaseChangeComp A f j) := by
  apply CompatibleIso.trans_right_cancel ((a.baseChange f).baseChange j)
  simp only [compatibleRefinementTransport, CompatibleIso.baseChange_trans,
    CompatibleIso.baseChange_symm, CompatibleIso.trans_assoc]
  rw [CompatibleIso.baseChange_comp_natural]
  simp only [CompatibleIso.symm_trans_assoc,
    CompatibleIso.symm_trans, CompatibleIso.trans_refl]
  exact congrArg (fun z ↦ c.trans z) (compatibleBaseChangeCompEq_assoc H p q r f j w v).symm

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
