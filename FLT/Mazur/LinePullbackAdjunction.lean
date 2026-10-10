/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineStructureProjection

/-!
# Pullback morphisms with a line target

When the structure inclusion is invertible, the projection formula makes
pullback fully faithful on morphisms with a line target. All comparisons
use the original adjunction unit and the actual pullback functor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.LinePullbackAdjunction
open ModuleSheafTensor StructureDirectImage
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsIso (unitMap f)]

/-- The line projection formula identifies the actual adjunction unit as an isomorphism. -/
lemma unit_isIso {N : S.Modules} (hN : LocallyFreeRankOne N) :
    IsIso ((pullbackPushforwardAdjunction f).unit.app N) := by
  have hm : IsIso (map (unitMap f) (𝟙 N)) := by
    change IsIso (congr (asIso (unitMap f)) (Iso.refl N)).hom
    infer_instance
  have hi : IsIso (map (unitMap f) (𝟙 N) ≫ (LineStructureProjection.iso f N hN).hom) :=
    inferInstance
  rw [LineStructureProjection.unit_compatibility, isIso_comp_left_iff] at hi
  exact hi

/-- Descent of actual pullback morphisms when the target is a line. -/
def homEquiv (M : S.Modules) {N : S.Modules} (hN : LocallyFreeRankOne N) :
    (M ⟶ N) ≃ ((pullback f).obj M ⟶ (pullback f).obj N) := by
  let _ := unit_isIso f hN
  exact ((pullbackPushforwardAdjunction f).homEquiv M ((pullback f).obj N) |>.trans
    (Iso.homCongr (Iso.refl M)
      (asIso ((pullbackPushforwardAdjunction f).unit.app N)).symm)).symm

/-- The forward comparison is exactly pullback, without a choice of line frames. -/
lemma homEquiv_apply (M : S.Modules) {N : S.Modules} (hN : LocallyFreeRankOne N)
    (a : M ⟶ N) : homEquiv f M hN a = (pullback f).map a := by
  let _ := unit_isIso f hN
  apply (homEquiv f M hN).symm.injective
  rw [Equiv.symm_apply_apply]
  change a = (𝟙 M ≫ (pullbackPushforwardAdjunction f).homEquiv M
    ((pullback f).obj N) ((pullback f).map a)) ≫
      inv ((pullbackPushforwardAdjunction f).unit.app N)
  rw [Category.id_comp, Adjunction.homEquiv_unit,
    (pullbackPushforwardAdjunction f).unit_naturality a]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- Pullback detects equality of maps with a line target. -/
lemma map_injective (M : S.Modules) {N : S.Modules} (hN : LocallyFreeRankOne N) :
    Function.Injective (fun a : M ⟶ N ↦ (pullback f).map a) := by
  intro a b h
  apply (homEquiv f M hN).injective
  simpa only [homEquiv_apply] using h

/-- Every map to a pulled line comes from the original base. -/
lemma map_surjective (M : S.Modules) {N : S.Modules} (hN : LocallyFreeRankOne N) :
    Function.Surjective (fun a : M ⟶ N ↦ (pullback f).map a) := by
  intro a
  obtain ⟨b, hb⟩ := (homEquiv f M hN).surjective a
  exact ⟨b, (homEquiv_apply f M hN b).symm.trans hb⟩

end FLT.Mazur.FCurve.LinePullbackAdjunction
