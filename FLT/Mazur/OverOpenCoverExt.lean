/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Equality of relative maps from open chart factorizations

Pulling an actual open cover back along a relative map produces enough relative
factorizations to check equality. The source retains its original base morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Equality can be checked on every restriction factoring through an actual open chart. -/
theorem over_hom_ext_of_openCover_factorizations {S : Scheme} {T V : Over S}
    {ι : Type} (U : ι → Over S) (c : ∀ i, U i ⟶ T)
    (hc : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (c i).left) ∈
      Scheme.zariskiPrecoverage T.left)
    (a b : V ⟶ T)
    (h : ∀ i {W : Over S} (d : W ⟶ V) (p : W ⟶ U i),
      d ≫ a = p ≫ c i → d ≫ a = d ≫ b) : a = b := by
  apply Over.OverMorphism.ext
  let C : T.left.OpenCover :=
    { I₀ := ι, X := fun i ↦ (U i).left, f := fun i ↦ (c i).left, mem₀ := hc }
  apply Scheme.Cover.hom_ext (C.pullback₁ a.left)
  intro i
  let W : Over S := Over.mk (pullback.fst a.left (c i).left ≫ V.hom)
  let d : W ⟶ V := Over.homMk (pullback.fst a.left (c i).left) rfl
  let p : W ⟶ U i := Over.homMk (pullback.snd a.left (c i).left) (by
    rw [← (c i).w, ← Category.assoc, ← pullback.condition, Category.assoc, a.w]
    rfl)
  have hp : d ≫ a = p ≫ c i := Over.OverMorphism.ext pullback.condition
  exact congrArg Over.Hom.left (h i d p hp)

end FLT.Mazur
