/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianOpenIsoRestriction
public import FLT.Mazur.ArtinianProperStructureSheaf
public import FLT.Mazur.ModuleSheafOpenIsoDetection

/-!
# Gluing the original pullback of functions across Cartesian open charts
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CartesianOpenFunctionSheaf
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme} (f : X ⟶ Y)

/-- Invertibility on an open restriction gives invertibility on every subopen. -/
theorem app_isIso_of_restriction (U V : Y.Opens) (hVU : V ≤ U)
    (hf : ∀ W, IsIso ((f ∣_ U).app W)) : IsIso (f.app V) := by
  have ht := hf (U.ι ⁻¹ᵁ V)
  rw [morphismRestrict_app, isIso_comp_right_iff] at ht
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hVU]
  exact he ▸ ht

variable {A B : Scheme} (e : A ⟶ B) (a : A ⟶ X) (b : B ⟶ Y)
  [IsOpenImmersion a] [IsOpenImmersion b] (H : IsPullback e a b f)

include H in
/-- An open Cartesian chart with unchanged functions identifies all subopen functions. -/
theorem app_isIso_of_chart (he : ∀ W, IsIso (e.app W))
    (V : Y.Opens) (hV : V ≤ b.opensRange) : IsIso (f.app V) := by
  apply app_isIso_of_restriction f b.opensRange V hV
  intro W
  rw [CartesianOpenIsoRestriction.restrict_eq e a b f H,
    Scheme.Hom.comp_app, Scheme.Hom.comp_app]
  let _ := he (b.isoOpensRange.hom ⁻¹ᵁ W)
  infer_instance

/-- Local identification of functions glues as the actual morphism of ring sheaves. -/
theorem structureMap_isIso_of_cover {ι : Type} (U : ι → Y.Opens)
    (hU : ∀ y : Y, ∃ j, y ∈ U j)
    (hf : ∀ j V, V ≤ U j → IsIso (f.app V)) :
    IsIso (ArtinianProperStructureSheaf.structureMap (q := f)) := by
  apply Sheaf.isIso_of_coversTop
    (FCurve.ModuleSheafOpenIsoDetection.coversTop_of_cover U hU)
  intro j
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro V
  exact hf j V.unop.left (leOfHom V.unop.hom)

end FLT.Mazur.CartesianOpenFunctionSheaf
