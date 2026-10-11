/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverOpenImageUnion
public import FLT.Mazur.TranslatedHilbertGluedDescent

/-!
# The actual union of translated Hilbert intersections on a test

The original intersections cover an open subscheme of the test. Their original
Picard classes descend to a unique map to the glued parameter scheme.
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

/-- The open union on the original test of all intersections in the chosen family. -/
def translatedHilbertTestUnion : Over (Spec (.of R)) :=
  overOpenImageUnion (fun i ↦ translatedHilbertOverlapArrow f (a i).1 (a i).2 T s)

/-- The actual open inclusion into the unchanged original test. -/
def translatedHilbertTestUnionι : translatedHilbertTestUnion f a T s ⟶ T :=
  overOpenImageUnionι (fun i ↦ translatedHilbertOverlapArrow f (a i).1 (a i).2 T s)

instance translatedHilbertTestUnionι_isOpenImmersion :
    IsOpenImmersion (translatedHilbertTestUnionι f a T s).left :=
  overOpenImageUnionι_isOpenImmersion _

instance translatedHilbertTestUnionι_mono : Mono (translatedHilbertTestUnionι f a T s) :=
  Over.mono_of_mono_left _

/-- The original intersection domains provide the covering arrows into the union. -/
def translatedHilbertTestUnionChart (i : ι) :
    translatedHilbertOverlapTest f (a i).1 (a i).2 T s ⟶ translatedHilbertTestUnion f a T s :=
  overOpenImageUnionMap (fun i ↦ translatedHilbertOverlapArrow f (a i).1 (a i).2 T s) i

@[reassoc (attr := simp)]
theorem translatedHilbertTestUnionChart_fac (i : ι) :
    translatedHilbertTestUnionChart f a T s i ≫ translatedHilbertTestUnionι f a T s =
      translatedHilbertOverlapArrow f (a i).1 (a i).2 T s :=
  overOpenImageUnionMap_fac _ _

/-- The original Picard section restricted to the union has one actual representative. -/
theorem translatedHilbertTestUnion_existsUnique :
    ∃! k : translatedHilbertTestUnion f a T s ⟶ translatedHilbertGluedTest f hL a,
      translatedHilbertGluedPoint f hL a _ k =
        (relativeFppfSheaf f).obj.map (translatedHilbertTestUnionι f a T s).op s := by
  apply translatedHilbertGluedPoint_of_fppf_charts f hL a _ _
    (fun i ↦ translatedHilbertOverlapTest f (a i).1 (a i).2 T s)
    (translatedHilbertTestUnionChart f a T s) (overOpenImageUnion_cover _) id
    (fun i ↦ translatedHilbertOverlapToParameter f (a i).1 hL (a i).2 T s)
  intro i
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rw [translatedHilbertTestUnionChart_fac]
  exact translatedHilbertOverlap_class f (a i).1 hL (a i).2 T s

/-- The constructed map from the actual open union to the glued parameter scheme. -/
def translatedHilbertTestUnionToGlued :
    translatedHilbertTestUnion f a T s ⟶ translatedHilbertGluedTest f hL a :=
  (translatedHilbertTestUnion_existsUnique f hL a T s).choose

/-- The map represents exactly the original section restricted to the union. -/
theorem translatedHilbertTestUnion_class :
    translatedHilbertGluedPoint f hL a _ (translatedHilbertTestUnionToGlued f hL a T s) =
      (relativeFppfSheaf f).obj.map (translatedHilbertTestUnionι f a T s).op s :=
  (translatedHilbertTestUnion_existsUnique f hL a T s).choose_spec.1

/-- The descended map retains each original intersection's parameter map. -/
@[reassoc]
theorem translatedHilbertTestUnionToGlued_chart (i : ι) :
    translatedHilbertTestUnionChart f a T s i ≫ translatedHilbertTestUnionToGlued f hL a T s =
      translatedHilbertOverlapToParameter f (a i).1 hL (a i).2 T s ≫
        translatedHilbertGluedArrow f hL a i := by
  apply translatedHilbertGluedPoint_injective f hL a
  rw [translatedHilbertGluedPoint_natural, translatedHilbertTestUnion_class,
    translatedHilbertGluedPoint_chart, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, translatedHilbertTestUnionChart_fac]
  exact (translatedHilbertOverlap_class f (a i).1 hL (a i).2 T s).symm

end FLT.Mazur.HilbertChart
