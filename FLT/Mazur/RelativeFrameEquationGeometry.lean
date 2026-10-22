/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameEquationSplitting
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Exact images and kernels of framed endpoint equations

Coordinate equation charts form an actual open cover of the full equation.
Its coefficient image is their union, and its exact ideal sheaf is the
intersection of their exact ideals. No radical or reduction is taken.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T Z : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (I : Type) [Fintype I] {b : T ⟶ S}
  (a : Over.mk b ⟶ distinctScheme E I) (h : E.left ⟶ Z) (y : T ⟶ Z)
local notation "f" => pullback.fst E.hom b ≫ h
local notation "g" => pullback.snd E.hom b ≫ y
local notation "s" i:max => testSection E I a i
local notation "j" i:max => equalizer.ι (s i ≫ f) (s i ≫ g)

omit [Etale E.hom] in
/-- Each full equation chart keeps exactly its original coefficient inclusion. -/
@[reassoc] theorem frameEquationMap_projection (i : I) :
    frameEquationMap E I a h y i ≫ equalizer.ι f g ≫ pullback.snd E.hom b = j i := by
  rw [frameEquationMap_ι_assoc, testSection_snd, Category.comp_id]

/-- Complete coordinate equations form an actual open cover of the whole equation scheme. -/
def frameEquationCover (ha : Set.range a.left ⊆ completeLocus E I) :
    (frameEquation E (b := b) h y).OpenCover where
  I₀ := I
  X := frameEquationChart E I a h y
  «f» := frameEquationMap E I a h y
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨frameEquationMap_cover E I a h y ha, fun _ ↦ inferInstance⟩

/-- The actual comparison image is the union of the full coordinate equation images. -/
theorem frameEquation_projection_range (ha : Set.range a.left ⊆ completeLocus E I) :
    Set.range (equalizer.ι f g ≫ pullback.snd E.hom b) = ⋃ i : I, Set.range (j i) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨i, v, rfl⟩ := (frameEquationCover E I a h y ha).exists_eq w
    apply Set.mem_iUnion.mpr
    refine ⟨i, v, ?_⟩
    exact (congrArg (fun k ↦ k v) (frameEquationMap_projection E I a h y i)).symm
  · intro hz
    obtain ⟨i, v, rfl⟩ := Set.mem_iUnion.mp hz
    refine ⟨frameEquationMap E I a h y i v, ?_⟩
    exact congrArg (fun k ↦ k v) (frameEquationMap_projection E I a h y i)

/-- The exact full ideal is the intersection of coordinate equation ideals. -/
theorem frameEquation_projection_kernel (ha : Set.range a.left ⊆ completeLocus E I)
    [QuasiCompact (equalizer.ι f g ≫ pullback.snd E.hom b)] :
    (equalizer.ι f g ≫ pullback.snd E.hom b).ker = ⨅ i : I, (j i).ker := by
  rw [← Scheme.Hom.iInf_ker_openCover_map_comp _ (frameEquationCover E I a h y ha)]
  congr 1
  funext i
  exact congrArg Scheme.Hom.ker (frameEquationMap_projection E I a h y i)

end FLT.Mazur.RelativeOrderedTuples
