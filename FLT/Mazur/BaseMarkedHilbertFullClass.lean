/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertFullUnion

/-!
# The full union retains the original Picard section and both base maps

The local full intersections cover their union. Sheaf separation proves that
the descended map has exactly the supplied original Picard class.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (V : Over (Spec (.of R))) {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
  (U : Over (Spec (.of R))) (s : (relativeFppfSheaf f).obj.obj (op U))

/-- The projection to the original test, with no fixed translation-base map. -/
def baseMarkedFullToTest : baseMarkedFullIntersection f V a U s ⟶ U :=
  baseMarkedFullInclusion f V a U s ≫ prod.fst

@[reassoc]
theorem baseMarkedFullChart_toTest (i : ι) :
    baseMarkedFullChart f V a U s i ≫ baseMarkedFullToTest f V a U s =
      variableHilbertOverlapToTest f (a i).1 V (a i).2 U s := by
  rw [baseMarkedFullToTest, ← Category.assoc, baseMarkedFullChart_inclusion]
  rfl

/-- The full map retains the independent translation-base coordinate. -/
@[reassoc]
theorem baseMarkedFullToGlued_base :
    baseMarkedFullToGlued f hL V a U s ≫ baseMarkedGluedBase f hL V a =
      baseMarkedFullInclusion f V a U s ≫ prod.snd := by
  apply Over.OverMorphism.ext
  apply (baseMarkedFullCover f V a U s).hom_ext
  intro i
  change ((baseMarkedFullChart f V a U s i) ≫
    (baseMarkedFullToGlued f hL V a U s ≫ baseMarkedGluedBase f hL V a)).left =
      ((baseMarkedFullChart f V a U s i) ≫
        (baseMarkedFullInclusion f V a U s ≫ prod.snd)).left
  rw [← Category.assoc, baseMarkedFullChart_toGlued, Category.assoc,
    baseMarkedGluedArrow_base, variableHilbertOverlapToChart_base,
    ← Category.assoc, baseMarkedFullChart_inclusion]

/-- The original Picard sheaf satisfies descent on the actual full-intersection cover. -/
theorem baseMarkedFull_isSheafFor :
    Presieve.IsSheafFor ((relativeFppfSheaf f).obj ⋙ forget CommGrpCat)
      (Presieve.ofArrows (fun i ↦ variableHilbertOverlap f (a i).1 V (a i).2 U s)
        (baseMarkedFullChart f V a U s)) := by
  have hs := (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommGrpCat)).mp
    (relativeFppfSheaf f).property
  rw [isSheaf_iff_isSheaf_of_type] at hs
  apply hs.isSheafFor
  rw [GrothendieckTopology.mem_over_iff, ← Sieve.ofArrows, Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck
    (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ (baseMarkedFullCover f V a U s).mem₀)

/-- The map into the glued scheme represents the supplied original Picard class. -/
theorem baseMarkedFullToGlued_class :
    baseMarkedGluedPoint f hL V a _ (baseMarkedFullToGlued f hL V a U s) =
      (relativeFppfSheaf f).obj.map (baseMarkedFullToTest f V a U s).op s := by
  apply (baseMarkedFull_isSheafFor f V a U s).isSeparatedFor.ext
  intro W k hk
  cases hk with
  | mk i =>
    change (relativeFppfSheaf f).obj.map (baseMarkedFullChart f V a U s i).op _ =
      (relativeFppfSheaf f).obj.map (baseMarkedFullChart f V a U s i).op _
    rw [← baseMarkedGluedPoint_natural, baseMarkedFullChart_toGlued,
      baseMarkedGluedPoint_chart, variableHilbertOverlap_class]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      baseMarkedFullChart_toTest]

/-- Both full projections distinguish every relative map into this intersection. -/
theorem baseMarkedFull_hom_ext {W : Over (Spec (.of R))}
    {p q : W ⟶ baseMarkedFullIntersection f V a U s}
    (ht : p ≫ baseMarkedFullToTest f V a U s = q ≫ baseMarkedFullToTest f V a U s)
    (hg : p ≫ baseMarkedFullToGlued f hL V a U s =
      q ≫ baseMarkedFullToGlued f hL V a U s) : p = q := by
  apply (cancel_mono (baseMarkedFullInclusion f V a U s)).mp
  apply prod.hom_ext
  · exact (Category.assoc _ _ _).trans (ht.trans (Category.assoc _ _ _).symm)
  · have hb := congrArg (fun k ↦ k ≫ baseMarkedGluedBase f hL V a) hg
    simpa only [Category.assoc, baseMarkedFullToGlued_base] using hb

end FLT.Mazur.HilbertChart
