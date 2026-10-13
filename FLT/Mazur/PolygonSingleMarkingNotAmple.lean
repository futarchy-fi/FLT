/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMarkedSections
public import FLT.Mazur.PolygonPureDimension
public import FLT.Mazur.CurveDivisorAmpleSupport

/-!
# A polygon marking misses every other complete component

The disjoint Laurent opens remain disjoint from the closure of the other
open. Thus the original section kernel has no support on any other complete
normalization component, including its boundary nodes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

include h in
/-- A Laurent open misses the entire closure of every different component. -/
theorem torus_component_disjoint {i j : Fin n} (hij : i ≠ j) :
    Disjoint (Set.range (torusToComponent K ≫ componentι K n i ≫ p).left)
      (Set.range (componentι K n j ≫ p).left) := by
  let _ := torus_isOpenImmersion K n hn p q h i
  rw [← PolygonComponentImages.closure_torus K n hn p q h j]
  exact (PolygonComponentDistinct.torus_disjoint K n hn p q h hij).closure_right
    (torusToComponent K ≫ componentι K n i ≫ p).left.isOpenEmbedding.isOpenMap.isOpen_range

include h in
/-- The actual section kernel has no support on any other complete polygon component. -/
theorem section_support_disjoint_component (a : Kˣ) {i j : Fin n} (hij : i ≠ j) :
    Disjoint ((sectionMap K n p a i).ker.support : Set C.left)
      (Set.range (componentι K n j ≫ p).left) := by
  let _ := PolygonSeparated.cocone K n hn p q h
  rw [FCurve.support_section_ker C.hom _ (section_base K n p a i)]
  apply (torus_component_disjoint K n hn p q h hij).mono_left
  rintro _ ⟨x, rfl⟩
  exact section_mem_torus K n p a i x

end FLT.Mazur.PolygonMarkedSections

/-!
# The single-point divisor is not ample on a reducible polygon

For at least two components, another complete component misses the original
marking. The component-support criterion rules out ampleness and any closed
projective tensor power of its actual Cartier line. The smooth single-point
cubic construction therefore cannot present the uncontracted closed polygon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Kˣ) (i : Fin n)

/-- The original single-point Cartier line cannot be ample when another component exists. -/
theorem section_not_ample (h₂ : 2 ≤ n) :
    ¬ AmpleLineBundle (divisorLineBundle (sectionMap K n p a i).ker
      (section_cartier K n p hn q h a i).1) := by
  let _ := PolygonProper.proper K n hn p q h
  let _ : IsFinite ((sectionMap K n p a i).ker.subschemeι ≫ C.hom) := by
    rw [← sectionImageIso_hom C.hom _ (section_base K n p a i)]
    infer_instance
  let _ : Nontrivial (Fin n) := ⟨⟨⟨0, hn⟩, ⟨1, h₂⟩, by simp⟩⟩
  obtain ⟨j, hj⟩ := exists_ne i
  intro ha
  obtain ⟨x, hx, hxj⟩ :=
    (divisor_ample_iff_meets_components C.hom (section_cartier K n p hn q h a i).1
      (PolygonPureDimension.pureDimension K n hn p q h)).mp ha _
        (PolygonComponentImages.mem_components K n hn p q h j)
  exact Set.disjoint_left.mp
    (section_support_disjoint_component K n hn p q h a hj.symm) hx hxj

/-- No positive tensor power of this original line gives a closed projective embedding. -/
theorem section_not_relativeAmple (h₂ : 2 ≤ n) :
    ¬ RelativeAmple C.hom (divisorLineBundle (sectionMap K n p a i).ker
      (section_cartier K n p hn q h a i).1) := by
  let _ := PolygonProper.proper K n hn p q h
  rw [relativeAmple_iff_relativelyAmpleLineBundle
    (section_cartier K n p hn q h a i).1.divisorLineBundle_locallyFreeRankOne,
    relativelyAmpleLineBundle_iff_of_affine C.hom]
  exact section_not_ample K n hn p q h a i h₂

end FLT.Mazur.PolygonMarkedSections
