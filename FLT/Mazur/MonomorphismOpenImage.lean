/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The largest open image with an inverse to a monomorphism

Glue every actual local inverse, retaining the original target scheme structure.
The resulting open need not cover the target or contain every image point.
No reduced stratum or hypothesis asserting existence of an inverse is inserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.MonomorphismOpenImage
set_option backward.isDefEq.respectTransparency false
variable {D K : Scheme.{u}} (m : D ⟶ K)

/-- Opens admitting an actual original-source arrow over their inclusion. -/
def Patches := {U : K.Opens // ∃ a : U.toScheme ⟶ D, a ≫ m = U.ι}

/-- The open in the original, possibly nonreduced target. -/
def locus : K.Opens := ⨆ U : Patches m, U.val

/-- Each local inverse patch lies inside the constructed open. -/
theorem patch_le (U : Patches m) : U.val ≤ locus m := le_iSup _ U

/-- A chosen inverse on a patch, with its coefficient equation proved by construction. -/
def localLift (U : Patches m) : U.val.toScheme ⟶ D := U.property.choose

@[reassoc]
theorem localLift_comp (U : Patches m) : localLift m U ≫ m = U.val.ι :=
  U.property.choose_spec

/-- The actual patches cover their union. -/
def cover : (locus m).toScheme.OpenCover where
  I₀ := Patches m
  X U := U.val.toScheme
  f U := K.homOfLE (patch_le m U)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    obtain ⟨U, hx⟩ := (Opens.mem_iSup.mp x.property)
    refine ⟨U, ⟨x.val, hx⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun a ↦ a ⟨x.val, hx⟩) (K.homOfLE_ι (patch_le m U))

variable [Mono m]

/-- Monicity forces agreement on the entire scheme intersection, including nilpotents. -/
theorem localLift_compatible (U V : Patches m) :
    pullback.fst ((cover m).f U) ((cover m).f V) ≫ localLift m U =
      pullback.snd ((cover m).f U) ((cover m).f V) ≫ localLift m V := by
  apply (cancel_mono m).mp
  rw [Category.assoc, Category.assoc, localLift_comp, localLift_comp]
  have h := congrArg (fun a ↦ a ≫ (locus m).ι)
    (pullback.condition (f := (cover m).f U) (g := (cover m).f V))
  simpa only [cover, Category.assoc, Scheme.homOfLE_ι] using h

/-- The inverse is constructed by gluing the actual local arrows. -/
def lift : (locus m).toScheme ⟶ D :=
  (cover m).glueMorphisms (localLift m) (localLift_compatible m)

@[reassoc]
theorem cover_lift (U : Patches m) : (cover m).f U ≫ lift m = localLift m U :=
  (cover m).ι_glueMorphisms _ _ U

/-- The glued inverse preserves the original target and its structure sheaf. -/
@[reassoc]
theorem lift_comp : lift m ≫ m = (locus m).ι := by
  apply (cover m).hom_ext
  intro U
  rw [← Category.assoc, cover_lift, localLift_comp]
  exact (K.homOfLE_ι (patch_le m U)).symm

omit [Mono m] in
/-- Every local inverse to the original monomorphism factors through this open. -/
theorem le_locus (U : K.Opens) (a : U.toScheme ⟶ D) (ha : a ≫ m = U.ι) :
    U ≤ locus m := patch_le m ⟨U, a, ha⟩

/-- The complete inverse image, not a selected source branch, is the constructed open. -/
def inverseImageIso : pullback m (locus m).ι ≅ (locus m).toScheme where
  hom := pullback.snd _ _
  inv := pullback.lift (lift m) (𝟙 _) (by rw [Category.id_comp, lift_comp])
  hom_inv_id := by
    apply pullback.hom_ext
    · apply (cancel_mono m).mp
      simp only [Category.assoc, pullback.lift_fst, lift_comp, pullback.condition,
        Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  inv_hom_id := by simp only [pullback.lift_snd]

/-- Every test in the open has a unique original lift, with no reduced-test restriction. -/
theorem test_lift {Z : Scheme.{u}} (a : Z ⟶ (locus m).toScheme) :
    ∃! b : Z ⟶ D, b ≫ m = a ≫ (locus m).ι := by
  refine ⟨a ≫ lift m, ?_, ?_⟩
  · dsimp only
    rw [Category.assoc, lift_comp]
  · intro b hb
    apply (cancel_mono m).mp
    rw [hb, Category.assoc, lift_comp]

omit [Mono m] in
/-- An actual open-immersion comparison has precisely its full image as this locus. -/
theorem locus_eq_opensRange [IsOpenImmersion m] : locus m = m.opensRange := by
  apply le_antisymm
  · refine iSup_le fun U ↦ ?_
    intro x hx
    exact ⟨localLift m U ⟨x, hx⟩,
      congrArg (fun a ↦ a ⟨x, hx⟩) (localLift_comp m U)⟩
  · apply le_locus m _ m.isoOpensRange.inv
    calc
      _ = m.isoOpensRange.inv ≫ m.isoOpensRange.hom ≫ m.opensRange.ι := by
        rw [Scheme.Hom.isoOpensRange_hom_ι]
      _ = _ := Iso.inv_hom_id_assoc _ _

end FLT.Mazur.MonomorphismOpenImage
