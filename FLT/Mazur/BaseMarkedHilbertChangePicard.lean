/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertGluedChange

/-!
# The original Picard class commutes with translation-base change

Descent uniqueness identifies the pulled-back glued section with the glued
section of the changed charts. This applies to every original relative test.
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
  {V W : Over (Spec (.of R))} (b : W ⟶ V)
  {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
local notation "aW" => fun i ↦ baseMarkedIndexChange f b (a i)

/-- Pulling back the actual glued section gives the section of the changed charts. -/
theorem baseMarkedGluedChange_picard :
    (relativeFppfSheaf f).obj.map (baseMarkedGluedChange f hL b a).op
        (baseMarkedGluedPicard f hL V a) = baseMarkedGluedPicard f hL W aW := by
  apply (baseMarkedGluedPicard_existsUnique f hL W aW).choose_spec.2
  intro i
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  change baseMarkedGluedPoint f hL V a _
    (baseMarkedGluedArrow f hL W aW i ≫ baseMarkedGluedChange f hL b a) = _
  rw [baseMarkedGluedChange_chart, baseMarkedGluedPoint_chart]
  simpa only [Category.id_comp, baseMarkedChartSection, baseMarkedIndexChange] using
    baseMarkedChartChange_class f hL b (a i) (𝟙 _)

/-- The original class is preserved on all tests, not just on chart sections. -/
theorem baseMarkedGluedChange_point {U : Over (Spec (.of R))}
    (k : U ⟶ baseMarkedGluedTest f hL W aW) :
    baseMarkedGluedPoint f hL V a U (k ≫ baseMarkedGluedChange f hL b a) =
      baseMarkedGluedPoint f hL W aW U k := by
  rw [baseMarkedGluedPoint_natural]
  change (relativeFppfSheaf f).obj.map k.op
    ((relativeFppfSheaf f).obj.map (baseMarkedGluedChange f hL b a).op _) = _
  rw [baseMarkedGluedChange_picard]
  rfl

/-- Equality after comparison still determines a source map if its source base is retained. -/
theorem baseMarkedGluedChange_hom_ext {U : Over (Spec (.of R))}
    (p q : U ⟶ baseMarkedGluedTest f hL W aW)
    (hb : p ≫ baseMarkedGluedBase f hL W aW = q ≫ baseMarkedGluedBase f hL W aW)
    (he : p ≫ baseMarkedGluedChange f hL b a = q ≫ baseMarkedGluedChange f hL b a) :
    p = q := by
  apply baseMarkedGluedPoint_injective_over f hL W aW p q hb
  rw [← baseMarkedGluedChange_point f hL b a p,
    ← baseMarkedGluedChange_point f hL b a q, he]

end FLT.Mazur.HilbertChart
