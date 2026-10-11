/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverOpenCoverExt

/-!
# Image containment from relative open chart factorizations

Pull back the actual target cover along a relative map. Containment on every
relative chart factorization implies containment of the entire original image.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Image containment can be checked on the original relative chart factorizations. -/
theorem over_range_subset_of_openCover_factorizations {S : Scheme} {T V Z : Over S}
    {ι : Type} (U : ι → Over S) (c : ∀ i, U i ⟶ T)
    (hc : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (c i).left) ∈
      Scheme.zariskiPrecoverage T.left)
    (a : V ⟶ T) (b : V ⟶ Z) (P : Set Z.left)
    (h : ∀ i {W : Over S} (d : W ⟶ V) (p : W ⟶ U i),
      d ≫ a = p ≫ c i → Set.range (d ≫ b).left ⊆ P) : Set.range b.left ⊆ P := by
  rintro _ ⟨x, rfl⟩
  let C : T.left.OpenCover :=
    { I₀ := ι, X := fun i ↦ (U i).left, f := fun i ↦ (c i).left, mem₀ := hc }
  let D := C.pullback₁ a.left
  let i := Scheme.Cover.idx D x
  obtain ⟨y, hy⟩ := Scheme.Cover.covers D x
  let W : Over S := Over.mk (pullback.fst a.left (c i).left ≫ V.hom)
  let d : W ⟶ V := Over.homMk (pullback.fst a.left (c i).left) rfl
  let p : W ⟶ U i := Over.homMk (pullback.snd a.left (c i).left) (by
    rw [← (c i).w, ← Category.assoc, ← pullback.condition, Category.assoc, a.w]
    rfl)
  have hp : d ≫ a = p ≫ c i := Over.OverMorphism.ext pullback.condition
  apply h i d p hp
  refine ⟨y, ?_⟩
  change b.left (d.left y) = b.left x
  exact congrArg b.left hy

end FLT.Mazur
