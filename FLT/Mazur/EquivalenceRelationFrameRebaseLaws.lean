/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniversalFrameRebase

/-!
# Functorial laws for scheme-level frame rebasing

Transporting an entire distinct frame commutes with arbitrary test change,
identity arrows and composition. The proofs use the original second endpoints,
without unfolding the chosen pullbacks or the distinct-tuple lift.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples EquivalenceRelationFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A T : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I]

local instance lawsOverFirst_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›

/-- Change the displayed base of a frame along an equality of actual morphisms. -/
def frameCast {b b' : T ⟶ A} (h : b = b')
    (t : Over.mk b ⟶ distinctScheme (Over.mk p) I) :
    Over.mk b' ⟶ distinctScheme (Over.mk p) I :=
  Over.homMk t.left (t.w.trans h)

/-- Pull a frame back along an arbitrary scheme test morphism. -/
def framePull {b : T ⟶ A} (t : Over.mk b ⟶ distinctScheme (Over.mk p) I)
    {U : Scheme} (z : U ⟶ T) : Over.mk (z ≫ b) ⟶ distinctScheme (Over.mk p) I :=
  Over.homMk (z ≫ t.left) (by rw [Category.assoc, t.w]; rfl)

/-- Rebasing is natural on arbitrary scheme tests, including nonreduced tests. -/
theorem rebaseFrame_natural (a : T ⟶ D)
    (t : Over.mk (a ≫ p) ⟶ distinctScheme (Over.mk p) I) {U : Scheme} (z : U ⟶ T) :
    (rebaseFrame e I (z ≫ a)
      (frameCast I (Category.assoc z a p).symm (framePull I t z))).left =
        z ≫ (rebaseFrame e I a t).left := by
  have h := frame_ext_second e I
    (u := rebaseFrame e I (z ≫ a)
      (frameCast I (Category.assoc z a p).symm (framePull I t z)))
    (v := frameCast I (Category.assoc z a q).symm
      (framePull I (rebaseFrame e I a t) z))
  apply congrArg Over.Hom.left (h ?_)
  intro i
  rw [rebaseFrame_second]
  change ((z ≫ t.left) ≫ (distinctCoordinate (Over.mk p) I i).left) ≫ q =
    ((z ≫ (rebaseFrame e I a t).left) ≫
      (distinctCoordinate (Over.mk p) I i).left) ≫ q
  simp only [Category.assoc]
  exact congrArg (fun r ↦ z ≫ r) (rebaseFrame_second e I a t i).symm

/-- An identity original arrow leaves the entire scheme-level frame unchanged. -/
theorem rebaseFrame_identity (b : T ⟶ A)
    (t : Over.mk b ⟶ distinctScheme (Over.mk p) I) :
    (rebaseFrame e I (b ≫ e.r) (frameCast I
      (by rw [Category.assoc, e.reflexivity₁, Category.comp_id]) t)).left = t.left := by
  have hb : b = (b ≫ e.r) ≫ q := by
    rw [Category.assoc, e.reflexivity₂, Category.comp_id]
  apply congrArg Over.Hom.left (frame_ext_second e I (v := frameCast I hb t) ?_)
  intro i
  exact rebaseFrame_second e I _ _ i

/-- Successive rebasing agrees with rebasing along the original composite arrow. -/
theorem rebaseFrame_comp (a b : T ⟶ D) (h : a ≫ q = b ≫ p)
    (t : Over.mk (a ≫ p) ⟶ distinctScheme (Over.mk p) I) :
    (rebaseFrame e I b (frameCast I h (rebaseFrame e I a t))).left =
      (rebaseFrame e I (compose e a b h)
        (frameCast I (compose_fst e a b h).symm t)).left := by
  apply congrArg Over.Hom.left (frame_ext_second e I
    (v := frameCast I (compose_snd e a b h)
      (rebaseFrame e I (compose e a b h)
        (frameCast I (compose_fst e a b h).symm t))) ?_)
  intro i
  rw [rebaseFrame_second]
  have h₁ := rebaseFrame_second e I a t i
  have h₂ := rebaseFrame_second e I (compose e a b h)
    (frameCast I (compose_fst e a b h).symm t) i
  dsimp only [frameCast, Over.homMk_left, Over.comp_left] at h₁ h₂ ⊢
  exact h₁.trans h₂.symm

end FLT.Mazur.EquivalenceRelationOrderedFrames
