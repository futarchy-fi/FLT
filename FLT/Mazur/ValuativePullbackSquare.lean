/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SpecializationValuationSquare
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Valuation extension through a full Cartesian envelope

A valuation square for a pullback projection gives a square for the original
map over the original coefficient scheme. A lift of either square constructs
a lift of the other. The source test, valuation ring, fraction field, and
independent translation map are all retained exactly.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.ValuativePullbackSquare
universe u
set_option backward.isDefEq.respectTransparency false
variable {E A V S : Scheme.{u}} {p : E ⟶ A} {r : E ⟶ V}
  {a : A ⟶ S} {v : V ⟶ S} (h : IsPullback p r a v) (D : ValuativeCommSq p)

/-- The valuation square on the unchanged coefficient scheme. -/
def baseSquare : ValuativeCommSq v where
  R := D.R
  K := D.K
  i₁ := D.i₁ ≫ r
  i₂ := D.i₂ ≫ a
  commSq := ⟨by rw [Category.assoc, ← h.w, ← Category.assoc, D.commSq.w,
    Category.assoc]⟩

/-- Extending the translation constructs the entire original envelope extension. -/
theorem hasLift_iff : (baseSquare h D).commSq.HasLift ↔ D.commSq.HasLift := by
  constructor
  · intro hl
    obtain ⟨l, hg, hc⟩ := hl.exists_lift
    dsimp only [baseSquare] at l hg hc
    refine ⟨⟨h.lift D.i₂ l hc.symm, ?_, h.lift_fst _ _ _⟩⟩
    apply h.hom_ext
    · rw [Category.assoc, h.lift_fst, ← D.commSq.w]
    · rw [Category.assoc, h.lift_snd]
      exact hg
  · intro hl
    obtain ⟨l, hg, hc⟩ := hl.exists_lift
    refine ⟨⟨l ≫ r, ?_, ?_⟩⟩
    · change Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ l ≫ r = D.i₁ ≫ r
      rw [← Category.assoc, hg]
    · change (l ≫ r) ≫ v = D.i₂ ≫ a
      rw [Category.assoc, ← h.w, ← Category.assoc, hc]

/-- A failure to extend the envelope is a failure on the actual original translation. -/
theorem no_lift (hn : ¬ D.commSq.HasLift) : ¬ (baseSquare h D).commSq.HasLift :=
  fun hl ↦ hn ((hasLift_iff h D).mp hl)

end FLT.Mazur.ValuativePullbackSquare
