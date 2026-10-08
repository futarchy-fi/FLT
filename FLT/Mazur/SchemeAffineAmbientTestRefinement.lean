/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineAmbientTestCocycle
public import FLT.Mazur.SchemeAffineSchemeTestRefinement
public import FLT.Mazur.ModuleSheafOverlapCoordinateRefinement

/-!
# Refinement of ambient test comparisons

The comparisons of ambient chart pushforwards respect arbitrary scheme
refinement, with the canonical pullback composition maps on both sides.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open ModuleSheafOverlapImageTransition
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y W Z : Scheme.{u}} {p : Y ⟶ X} (C C' : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable [IsOpenImmersion C.base] [IsOpenImmersion C'.base]
attribute [local irreducible] sheaf schemeTestComparison coordinateIso

/-- Ambient chart comparisons commute with further pullback. -/
theorem ambientTestComparison_refine (t : Z ⟶ W) (a : W ⟶ X)
    (i : W ⟶ Spec C.baseRing) (j : W ⟶ Spec C'.baseRing)
    (hi : i ≫ C.base = a) (hj : j ≫ C'.base = a) :
    (pullback t).map (C.ambientTestComparison C' D a i j hi hj) ≫
        (pullbackComp t a).hom.app ((pushforward C'.base).obj (C'.sheaf D)) =
      (pullbackComp t a).hom.app ((pushforward C.base).obj (C.sheaf D)) ≫
        C.ambientTestComparison C' D (t ≫ a) (t ≫ i) (t ≫ j)
          (by rw [Category.assoc, hi]) (by rw [Category.assoc, hj]) := by
  have hci := coordinateIso_refine t i C.base a hi (t ≫ i) (t ≫ a) rfl rfl
    (by rw [Category.assoc, hi]) (C.sheaf D)
  have hcj := coordinateIso_refine t j C'.base a hj (t ≫ j) (t ≫ a) rfl rfl
    (by rw [Category.assoc, hj]) (C'.sheaf D)
  simp only [SheafPullbackPathComparison.comparison, pullbackCongr,
    eqToIso_refl, Iso.trans_refl] at hci hcj
  apply (cancel_mono (coordinateIso (t ≫ j) C'.base (t ≫ a)
    (by rw [Category.assoc, hj]) (C'.sheaf D)).hom).mp
  simp only [ambientTestComparison, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [← hcj]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Functor.map_comp, Category.assoc, schemeTestComparison_refine,
    ← Category.assoc, hci, Category.assoc]

end FLT.Mazur.SchemeAffineDescent.Chart
