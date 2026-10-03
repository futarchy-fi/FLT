/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MultiplicativeGroupDimension
public import FLT.Mazur.PolygonActionTranslation
public import FLT.Mazur.PolygonComponentDistinct
public import FLT.Mazur.SmoothOpenSectionCartier

/-!
# Smooth marked sections of a polygon

A unit on each normalization component gives an actual section in its Laurent
open. Each section is a relative Cartier divisor on the whole polygon, and
sections on different components have disjoint images.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching ProjectiveLineActionSpecialization
variable (K : Type u) [Field K] (n : ℕ)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C)

/-- The section defined by a unit in a specified Laurent component. -/
def sectionMap (a : Kˣ) (i : Fin n) : Spec (.of K) ⟶ C.left :=
  unitPoint K a ≫ (torusToComponent K ≫ componentι K n i ≫ p).left

/-- The marked point is a section of the actual structure morphism. -/
@[reassoc (attr := simp)]
theorem section_base (a : Kˣ) (i : Fin n) :
    sectionMap K n p a i ≫ C.hom = 𝟙 _ := by
  rw [sectionMap, Category.assoc, Over.w]
  exact unitPoint_base K a

/-- Every value of a marked section lies in its Laurent open. -/
theorem section_mem_torus (a : Kˣ) (i : Fin n) (x : Spec (.of K)) :
    sectionMap K n p a i x ∈
      Set.range (torusToComponent K ≫ componentι K n i ≫ p).left :=
  ⟨unitPoint K a x, rfl⟩

variable [NeZero n] (hn : 0 < n) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- A marked section is Cartier even at the level of the entire singular polygon. -/
theorem section_cartier (a : Kˣ) (i : Fin n) :
    FCurve.RelativeEffectiveCartier C.hom (sectionMap K n p a i).ker := by
  let j := torusToComponent K ≫ componentι K n i ≫ p
  let := torus_isOpenImmersion K n hn p q h i
  let := PolygonSeparated.cocone K n hn p q h
  have hd : SmoothOfRelativeDimension 1 (j.left ≫ C.hom) := by
    rw [Over.w]
    exact MultiplicativeGroupDimension.dimension K
  exact FCurve.smoothOpenSectionCartier j.left C.hom (unitPoint K a)
    inferInstance hd inferInstance (by
      rw [Over.w]
      exact unitPoint_base K a)

include h in
/-- Marked sections on distinct components have disjoint images. -/
theorem section_disjoint (a b : Kˣ) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Set.range (sectionMap K n p a i)) (Set.range (sectionMap K n p b j)) := by
  apply (PolygonComponentDistinct.torus_disjoint K n hn p q h hij).mono
  · rintro _ ⟨x, rfl⟩
    exact section_mem_torus K n p a i x
  · rintro _ ⟨x, rfl⟩
    exact section_mem_torus K n p b j x

end FLT.Mazur.PolygonMarkedSections
