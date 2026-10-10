/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DisjointClosedCoproduct
public import FLT.Mazur.SectionDivisors

/-!
# Universal distinctness and disjoint section images

Sections distinct on every nonempty test scheme have disjoint images over any
base. A coincidence would give a nonempty pullback on which two sections agree.
For a finite family on a separated scheme this constructs a closed immersion
of the coproduct and identifies its ideal with the product of section ideals.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace FLT.Mazur.UniversallyDistinctSections

variable {S : Scheme} {X : Over S} {Index : Type}
  (s : Index → (𝟙_ (Over S) ⟶ X))

/-- Distinctness is tested after all nonempty scheme maps into the base. -/
def UniversallyDistinct : Prop :=
  ∀ (V : Over S) (g : V ⟶ 𝟙_ (Over S)), Nonempty V.left →
    Function.Injective (fun i ↦ g ≫ s i)

/-- Universal distinctness rules out all intersections of the section images. -/
theorem disjoint (hs : UniversallyDistinct s) :
    Pairwise fun i j ↦ Disjoint (Set.range (s i).left) (Set.range (s j).left) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  let a : S ⟶ X.left := (s i).left
  let b : S ⟶ X.left := (s j).left
  have ha : a ≫ X.hom = 𝟙 S := (s i).w
  have hb : b ≫ X.hom = 𝟙 S := (s j).w
  have he : pullback.fst a b = pullback.snd a b := by
    calc
      pullback.fst a b = pullback.fst a b ≫ a ≫ X.hom := by rw [ha, Category.comp_id]
      _ = pullback.snd a b ≫ b ≫ X.hom := by rw [pullback.condition_assoc]
      _ = pullback.snd a b := by rw [hb, Category.comp_id]
  let V : Over S := Over.mk (pullback.fst a b)
  let g : V ⟶ 𝟙_ (Over S) := Over.homMk (pullback.fst a b) (by simp [V])
  obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
  apply hij
  apply hs V g ⟨z⟩
  apply Over.OverMorphism.ext
  change pullback.fst a b ≫ a = pullback.fst a b ≫ b
  rw [pullback.condition, he]

variable [Finite Index] [IsSeparated X.hom]

/-- The universally distinct section family is a closed subscheme. -/
theorem closed (hs : UniversallyDistinct s) :
    IsClosedImmersion (Sigma.desc fun i ↦ (s i).left) := by
  have (i : Index) : IsClosedImmersion (s i).left :=
    FCurve.isClosedImmersion_section X.hom _ (s i).w
  exact DisjointClosedCoproduct.closed _ (disjoint s hs)

variable [Fintype Index]

/-- The actual closed subscheme retains every section with multiplicity one. -/
theorem product_eq_kernel (hs : UniversallyDistinct s) :
    (∏ i, (s i).left.ker) = (Sigma.desc fun i ↦ (s i).left).ker := by
  have (i : Index) : IsClosedImmersion (s i).left :=
    FCurve.isClosedImmersion_section X.hom _ (s i).w
  exact DisjointClosedCoproduct.product_eq_kernel _ (disjoint s hs)

end FLT.Mazur.UniversallyDistinctSections
