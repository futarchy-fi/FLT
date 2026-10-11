/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TranslatedHilbertTestUnion
public import FLT.Mazur.OverOpenCoverImage

/-!
# The full test-map universal property of the open union

Every pair consisting of an original test map and a glued parameter map with
equal original Picard classes factors uniquely through the actual open union.
This proves the entire scheme-valued intersection, including nonreduced tests.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {ι : Type} (a : ι → TranslatedHilbertIndex f)
  (T : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op T))

/-- Equality of original classes forces the entire test image into the actual open union. -/
theorem translatedHilbertTestUnion_range {U : Over (Spec (.of R))}
    (b : U ⟶ T) (k : U ⟶ translatedHilbertGluedTest f hL a)
    (hk : translatedHilbertGluedPoint f hL a U k = (relativeFppfSheaf f).obj.map b.op s) :
    Set.range b.left ⊆ (openImageUnion
      (fun i ↦ (translatedHilbertOverlapArrow f (a i).1 (a i).2 T s).left) : Set T.left) := by
  apply over_range_subset_of_openCover_factorizations
    (fun i ↦ acyclicHilbertTest f (a i).1) (translatedHilbertGluedArrow f hL a)
    (translatedHilbertGluedCover f hL a).mem₀ k b
  intro i W d p hdp
  have hp : translatedHilbertPicardPoint f (a i).1 hL (a i).2 W p =
      (relativeFppfSheaf f).obj.map (d ≫ b).op s := by
    rw [← translatedHilbertGluedPoint_chart f hL a i, ← hdp,
      translatedHilbertGluedPoint_natural, hk]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  obtain ⟨l, hl, _⟩ := translatedHilbertOverlap_lift f (a i).1 hL (a i).2 T s (d ≫ b) p hp
  rintro _ ⟨x, rfl⟩
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨i, l.left x, ?_⟩
  exact congrArg (fun z ↦ z.left x) hl.1

/-- The full fiber-product property, on every original relative test. -/
theorem translatedHilbertTestUnion_lift {U : Over (Spec (.of R))}
    (b : U ⟶ T) (k : U ⟶ translatedHilbertGluedTest f hL a)
    (hk : translatedHilbertGluedPoint f hL a U k = (relativeFppfSheaf f).obj.map b.op s) :
    ∃! q : U ⟶ translatedHilbertTestUnion f a T s,
      q ≫ translatedHilbertTestUnionι f a T s = b ∧
        q ≫ translatedHilbertTestUnionToGlued f hL a T s = k := by
  obtain ⟨q, hq, huniq⟩ := overOpenImageUnion_lift
    (fun i ↦ translatedHilbertOverlapArrow f (a i).1 (a i).2 T s) b
    (translatedHilbertTestUnion_range f hL a T s b k hk)
  change q ≫ translatedHilbertTestUnionι f a T s = b at hq
  refine ⟨q, ⟨hq, ?_⟩, fun l hl ↦ huniq l hl.1⟩
  apply translatedHilbertGluedPoint_injective f hL a U
  rw [translatedHilbertGluedPoint_natural, translatedHilbertTestUnion_class,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hq]
  exact hk.symm

end FLT.Mazur.HilbertChart
