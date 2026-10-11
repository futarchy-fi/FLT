/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertGluedMap
public import FLT.Mazur.OverOpenCoverExt

/-!
# Original class and translation base distinguish maps to the glued scheme

The original chart classes and base maps distinguish local maps. Pulling back the actual
open chart cover twice shows the global map distinguishes every relative test.
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

/-- The original class distinguishes maps with the same translation-base map. -/
theorem baseMarkedGluedPoint_injective_over {U : Over (Spec (.of R))}
    (p q : U ⟶ baseMarkedGluedTest f hL V a)
    (hb : p ≫ baseMarkedGluedBase f hL V a = q ≫ baseMarkedGluedBase f hL V a)
    (hpq : baseMarkedGluedPoint f hL V a U p = baseMarkedGluedPoint f hL V a U q) :
    p = q := by
  apply over_hom_ext_of_openCover_factorizations
    (fun i ↦ variableHilbertTest f (a i).1 V) (baseMarkedGluedArrow f hL V a)
    (baseMarkedGluedCover f hL V a).mem₀ p q
  intro i T d u hdu
  symm
  apply over_hom_ext_of_openCover_factorizations
    (fun i ↦ variableHilbertTest f (a i).1 V) (baseMarkedGluedArrow f hL V a)
    (baseMarkedGluedCover f hL V a).mem₀ (d ≫ q) (d ≫ p)
  intro j W e v hev
  have hleft : e ≫ (d ≫ p) = (e ≫ u) ≫ baseMarkedGluedArrow f hL V a i := by
    rw [hdu, Category.assoc]
  have hc : baseMarkedGluedPoint f hL V a W (e ≫ (d ≫ p)) =
      baseMarkedGluedPoint f hL V a W (e ≫ (d ≫ q)) := by
    simpa only [← baseMarkedGluedPoint_natural, Category.assoc] using
      congrArg ((relativeFppfSheaf f).obj.map (e ≫ d).op) hpq
  rw [hleft, hev, baseMarkedGluedPoint_chart, baseMarkedGluedPoint_chart] at hc
  have hbase : v ≫ variableHilbertBase f (a j).1 V =
      (e ≫ u) ≫ variableHilbertBase f (a i).1 V := by
    rw [← baseMarkedGluedArrow_base f hL V a j,
      ← baseMarkedGluedArrow_base f hL V a i,
      ← Category.assoc, ← Category.assoc, ← hev, ← hleft]
    simpa only [Category.assoc] using congrArg (fun m ↦ (e ≫ d) ≫ m) hb.symm
  exact hev.trans ((baseMarkedGlued_chart_class_eq f hL V a i j (e ≫ u) v hbase hc).symm.trans
    hleft.symm)

end FLT.Mazur.HilbertChart
