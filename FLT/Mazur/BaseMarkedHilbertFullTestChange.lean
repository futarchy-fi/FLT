/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertFullLift

/-!
# Changing the original test of a full Picard intersection

Pull back the original Picard section along a test map. The constructed map
between the full intersections retains the glued endpoint and the test map.
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
  {U W : Over (Spec (.of R))} (b : W ⟶ U)
  (s : (relativeFppfSheaf f).obj.obj (op U))
local notation "sW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) b.op s

/-- The original glued endpoint class is the unchanged original test section's restriction. -/
theorem baseMarkedFullTestChange_class :
    baseMarkedGluedPoint f hL V a _ (baseMarkedFullToGlued f hL V a W sW) =
      (relativeFppfSheaf f).obj.map (baseMarkedFullToTest f V a W sW ≫ b).op s := by
  rw [baseMarkedFullToGlued_class]
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- The actual comparison after changing the original test and its Picard section. -/
def baseMarkedFullTestChange : baseMarkedFullIntersection f V a W sW ⟶
    baseMarkedFullIntersection f V a U s :=
  baseMarkedFullLift f hL V a U s (baseMarkedFullToTest f V a W sW ≫ b)
    (baseMarkedFullToGlued f hL V a W sW) (baseMarkedFullTestChange_class f hL V a b s)

@[reassoc]
theorem baseMarkedFullTestChange_test :
    baseMarkedFullTestChange f hL V a b s ≫ baseMarkedFullToTest f V a U s =
      baseMarkedFullToTest f V a W sW ≫ b :=
  baseMarkedFullLift_toTest f hL V a U s _ _ _

@[reassoc]
theorem baseMarkedFullTestChange_glued :
    baseMarkedFullTestChange f hL V a b s ≫ baseMarkedFullToGlued f hL V a U s =
      baseMarkedFullToGlued f hL V a W sW :=
  baseMarkedFullLift_toGlued f hL V a U s _ _ _

/-- The independent translation-base map is retained by this comparison. -/
@[reassoc]
theorem baseMarkedFullTestChange_base :
    baseMarkedFullTestChange f hL V a b s ≫ baseMarkedFullInclusion f V a U s ≫ prod.snd =
      baseMarkedFullInclusion f V a W sW ≫ prod.snd := by
  rw [← baseMarkedFullToGlued_base f hL V a U s, ← Category.assoc,
    baseMarkedFullTestChange_glued, baseMarkedFullToGlued_base]

end FLT.Mazur.HilbertChart
