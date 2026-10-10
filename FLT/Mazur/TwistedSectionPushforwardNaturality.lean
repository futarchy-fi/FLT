/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TwistedSectionPushforward

/-!
# Naturality and nonvanishing of the direct-image correspondence

Changing the coefficient sheaf acts by the actual pushforward map. The
correspondence also preserves zero and hence detects nonzero sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor
variable {X S : Scheme.{u}}

/-- Tensoring the zero coefficient morphism gives the zero morphism of sheaves. -/
lemma tensorMap_zero_left (M P B : X.Modules) : map (0 : M ⟶ P) (𝟙 B) = 0 := by
  apply ModuleSheafTensor.hom_ext
  intro U m b
  rw [ModuleSheafTensor.map_pure]
  change ModuleSheafTensor.pure P B U 0 b = 0
  simp only [ModuleSheafTensor.pure, TensorProduct.zero_tmul]
  exact map_zero ((unit P B).app (.op U)).hom

/-- Tensor duality carries the zero dual-line morphism to the zero section. -/
lemma lineHomSectionEquiv_zero (L : X.Modules) {B : X.Modules}
    (hB : LocallyFreeRankOne B) : lineHomSectionEquiv L hB 0 = 0 := by
  have h := lineHomSectionEquiv_hom L hB 0
  rw [tensorMap_zero_left, Limits.comp_zero] at h
  have he := congrArg (fun a : structureModule X ⟶ tensor L B ↦
    a.app ⊤ (1 : Γ(X, ⊤))) h
  rw [globalSectionHom_top] at he
  exact he

/-- The inverse tensor correspondence also preserves zero. -/
lemma lineHomSectionEquiv_symm_zero (L : X.Modules) {B : X.Modules}
    (hB : LocallyFreeRankOne B) : (lineHomSectionEquiv L hB).symm 0 = 0 :=
  (lineHomSectionEquiv L hB).symm_apply_eq.mpr (lineHomSectionEquiv_zero L hB).symm

/-- The inverse tensor correspondence commutes with actual coefficient maps. -/
lemma lineHomSectionEquiv_symm_naturality {L P B : X.Modules}
    (hB : LocallyFreeRankOne B) (s : Γ(tensor L B, ⊤)) (b : L ⟶ P) :
    (lineHomSectionEquiv P hB).symm ((map b (𝟙 B)).app ⊤ s) =
      (lineHomSectionEquiv L hB).symm s ≫ b := by
  apply (lineHomSectionEquiv P hB).injective
  rw [Equiv.apply_symm_apply, lineHomSectionEquiv_naturality, Equiv.apply_symm_apply]

/-- Changing coefficients on the total space acts by the actual direct-image map. -/
lemma twistedSectionPushforwardEquiv_naturality (f : X ⟶ S) {L P : X.Modules}
    {B : S.Modules} (hB : LocallyFreeRankOne B)
    (s : Γ(tensor L ((pullback f).obj B), ⊤)) (b : L ⟶ P) :
    twistedSectionPushforwardEquiv f P hB ((map b (𝟙 _)).app ⊤ s) =
      twistedSectionPushforwardEquiv f L hB s ≫ (pushforward f).map b := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).symm.injective
  rw [twistedSectionPushforwardEquiv_adjoint,
    Adjunction.homEquiv_naturality_right_symm, twistedSectionPushforwardEquiv_adjoint,
    lineHomSectionEquiv_symm_naturality, Category.assoc]

/-- The actual direct-image correspondence preserves zero. -/
lemma twistedSectionPushforwardEquiv_zero (f : X ⟶ S) (L : X.Modules)
    {B : S.Modules} (hB : LocallyFreeRankOne B) :
    twistedSectionPushforwardEquiv f L hB 0 = 0 := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).symm.injective
  rw [twistedSectionPushforwardEquiv_adjoint, lineHomSectionEquiv_symm_zero]
  simp only [Limits.comp_zero, Adjunction.homEquiv_symm_apply, Functor.map_zero,
    Limits.zero_comp]

/-- Nonvanishing can be checked on the actual map into the direct image. -/
theorem twistedSectionPushforwardEquiv_ne_zero_iff (f : X ⟶ S) (L : X.Modules)
    {B : S.Modules} (hB : LocallyFreeRankOne B)
    (s : Γ(tensor L ((pullback f).obj B), ⊤)) :
    twistedSectionPushforwardEquiv f L hB s ≠ 0 ↔ s ≠ 0 := by
  rw [← twistedSectionPushforwardEquiv_zero f L hB,
    (twistedSectionPushforwardEquiv f L hB).injective.ne_iff]

end FLT.Mazur.FCurve
