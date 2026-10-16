/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFrameRebaseLaws

/-!
# Completeness of rebased frames for an arbitrary scheme equivalence relation

The scheme-level frame construction induces the original whole-fiber isomorphism
on every geometric coordinate. Hence completeness is preserved without discarding
any original relation arrows or assuming an open completeness neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples EquivalenceRelationFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I]
  {K : Type} [Field K] (a : Spec (.of K) ⟶ D)

local instance geometricOverFirst_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local notation "E" => Over.mk p
variable (t : Over.mk (a ≫ p) ⟶ distinctScheme (Over.mk p) I)

/-- Each rebased geometric section is transported by the whole original fiber isomorphism. -/
theorem rebaseFrame_geometric (i : I) :
    geometricCoordinate E I (K := K) (b := a ≫ q) (rebaseFrame e I a t) i =
      geometricCoordinate E I (K := K) (b := a ≫ p) t i ≫ (rebaseIso e a).hom := by
  have hs : geometricCoordinate E I t i ≫ pullback.snd p (a ≫ p) = 𝟙 _ :=
    geometricCoordinate_snd E I t i
  have hf : geometricCoordinate E I t i ≫ pullback.fst p (a ≫ p) =
      (t ≫ distinctCoordinate E I i).left := geometricCoordinate_fst E I t i
  apply pullback.hom_ext
  · rw [geometricCoordinate_fst]
    apply e.right_cancellation
    · have ht := (rebaseFrame e I a t ≫ distinctCoordinate E I i).w
      change _ ≫ p = ((geometricCoordinate E I (K := K) (b := a ≫ p) t i ≫ rebase e a) ≫
        pullback.fst p (a ≫ q)) ≫ p
      simp only [Category.assoc, rebase_fst_assoc, rebaseArrow_fst]
      rw [← Category.assoc, hs, Category.id_comp]
      exact ht
    · change _ ≫ q = ((geometricCoordinate E I (K := K) (b := a ≫ p) t i ≫ rebase e a) ≫
        pullback.fst p (a ≫ q)) ≫ q
      simp only [Category.assoc, rebase_fst_assoc, rebaseArrow_snd]
      rw [← Category.assoc, hf]
      exact rebaseFrame_second e I a t i
  · change _ = (geometricCoordinate E I (K := K) (b := a ≫ p) t i ≫ rebase e a) ≫
      pullback.snd p (a ≫ q)
    rw [Category.assoc, rebase_snd, geometricCoordinate_snd, hs]

/-- Completeness of the full geometric fiber is retained by scheme-level rebasing. -/
theorem rebaseFrame_complete
    (ht : Function.Bijective (fun i ↦ geometricCoordinate E I (K := K) (b := a ≫ p) t i default)) :
    Function.Bijective (fun i ↦ geometricCoordinate E I (K := K) (b := a ≫ q)
      (rebaseFrame e I a t) i default) := by
  have h := (rebaseIso e a).hom.homeomorph.bijective.comp ht
  have he (i : I) := congrArg
    (fun z : Spec (.of K) ⟶ pullback p (a ≫ q) ↦ z default)
    (rebaseFrame_geometric e I a t i)
  constructor
  · intro i j hij
    exact h.1 ((he i).symm.trans (hij.trans (he j)))
  · intro x
    obtain ⟨i, hi⟩ := h.2 x
    exact ⟨i, (he i).trans hi⟩

/-- Changing only the displayed base retains completeness of a geometric frame. -/
theorem frameCast_complete {b b' : Spec (.of K) ⟶ A} (h : b = b')
    (v : Over.mk b ⟶ distinctScheme E I)
    (hv : Function.Bijective (fun i ↦ geometricCoordinate E I (K := K) (b := b) v i default)) :
    Function.Bijective (fun i ↦ geometricCoordinate E I (K := K) (b := b')
      (frameCast I h v) i default) := by
  cases h
  exact hv

end FLT.Mazur.EquivalenceRelationOrderedFrames
