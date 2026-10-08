/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossRefinementBaseChoice

/-!
# Ordinary restriction squares for independent cross refinements

The heterogeneous choice theorem gives an ordinary morphism equality after
inserting the canonical pullback comparisons for equal base maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Equality of maps with equal pullback presentations gives the transport square. -/
theorem pullbackCongr_square_of_heq {U V W : Scheme.{u}}
    {f f' : U ⟶ V} {g g' : U ⟶ W} (hf : f = f') (hg : g = g')
    {A : V.Modules} {B : W.Modules}
    (a : (pullback f).obj A ⟶ (pullback g).obj B)
    (b : (pullback f').obj A ⟶ (pullback g').obj B) (h : HEq a b) :
    a ≫ (pullbackCongr hg).hom.app B = (pullbackCongr hf).hom.app A ≫ b := by
  subst f' g'
  cases h
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Category.id_comp]

variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p}
variable (ρ σ : C.CrossRefinement C')
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
attribute [local irreducible] effectiveComparison AffineRefinementPullback.compositionChart

/-- The ordinary comparison square permits independent common covers after base change. -/
theorem effectiveComparison_base_square (α : ρ.baseRing ⟶ σ.baseRing)
    (hl : ρ.leftBase ≫ α = σ.leftBase) (hr : ρ.rightBase ≫ α = σ.rightBase) :
    (pullback (Spec.map α)).map (ρ.effectiveComparison D).hom ≫
        (AffineRefinementPullback.compositionChart ρ.rightBase α (C'.sheaf D)).hom ≫
        (pullbackCongr (congrArg Spec.map hr)).hom.app (C'.sheaf D) =
      (AffineRefinementPullback.compositionChart ρ.leftBase α (C.sheaf D)).hom ≫
        (pullbackCongr (congrArg Spec.map hl)).hom.app (C.sheaf D) ≫
        (σ.effectiveComparison D).hom := by
  have h := pullbackCongr_square_of_heq (congrArg Spec.map hl) (congrArg Spec.map hr)
    _ _ (ρ.effectiveComparison_base_choice_independent σ D α hl hr)
  apply (cancel_epi
    (AffineRefinementPullback.compositionChart ρ.leftBase α (C.sheaf D)).inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
