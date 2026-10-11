/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertFullLiftRange

/-!
# The full intersection's universal property on original relative tests

An original glued point and a test map with the same Picard class have one
and only one lift. The independent translation-base coordinate is recovered
from the given glued point, rather than imposed as a hypothesis.
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
  {W : Over (Spec (.of R))} (b : W ⟶ U) (k : W ⟶ baseMarkedGluedTest f hL V a)
  (hk : baseMarkedGluedPoint f hL V a W k = (relativeFppfSheaf f).obj.map b.op s)

/-- Construct the unique full lift using the proved containment in the actual open. -/
def baseMarkedFullLift : W ⟶ baseMarkedFullIntersection f V a U s := by
  let t := prod.lift b (k ≫ baseMarkedGluedBase f hL V a)
  let l := IsOpenImmersion.lift (baseMarkedFullInclusion f V a U s).left t.left
    (baseMarkedFull_lift_range f hL V a U s b k hk)
  exact Over.homMk l (by
    rw [← (baseMarkedFullInclusion f V a U s).w, ← Category.assoc,
      IsOpenImmersion.lift_fac, Over.w])

@[reassoc]
theorem baseMarkedFullLift_inclusion :
    baseMarkedFullLift f hL V a U s b k hk ≫ baseMarkedFullInclusion f V a U s =
      prod.lift b (k ≫ baseMarkedGluedBase f hL V a) := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (baseMarkedFullInclusion f V a U s).left _ _

@[reassoc]
theorem baseMarkedFullLift_toTest :
    baseMarkedFullLift f hL V a U s b k hk ≫ baseMarkedFullToTest f V a U s = b := by
  rw [baseMarkedFullToTest, ← Category.assoc, baseMarkedFullLift_inclusion]
  exact prod.lift_fst _ _

@[reassoc]
theorem baseMarkedFullLift_toGlued :
    baseMarkedFullLift f hL V a U s b k hk ≫ baseMarkedFullToGlued f hL V a U s = k := by
  apply baseMarkedGluedPoint_injective_over f hL V a
  · rw [Category.assoc, baseMarkedFullToGlued_base, ← Category.assoc,
      baseMarkedFullLift_inclusion, prod.lift_snd]
  · rw [baseMarkedGluedPoint_natural, baseMarkedFullToGlued_class]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      baseMarkedFullLift_toTest]
    exact hk.symm

include hk in
/-- The full test intersection represents all class-compatible pairs uniquely. -/
theorem baseMarkedFull_lift :
    ∃! l : W ⟶ baseMarkedFullIntersection f V a U s,
      l ≫ baseMarkedFullToTest f V a U s = b ∧
        l ≫ baseMarkedFullToGlued f hL V a U s = k := by
  refine ⟨baseMarkedFullLift f hL V a U s b k hk,
    ⟨baseMarkedFullLift_toTest f hL V a U s b k hk,
      baseMarkedFullLift_toGlued f hL V a U s b k hk⟩, ?_⟩
  intro l hl
  exact baseMarkedFull_hom_ext f hL V a U s
    (hl.1.trans (baseMarkedFullLift_toTest f hL V a U s b k hk).symm)
    (hl.2.trans (baseMarkedFullLift_toGlued f hL V a U s b k hk).symm)

end FLT.Mazur.HilbertChart
