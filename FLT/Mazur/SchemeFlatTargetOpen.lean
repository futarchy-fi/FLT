/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The largest target open with flat whole-source projection

Target locality of flatness assembles all flat restrictions into one actual
flat projection. The source is the entire inverse image; no branch or reduced
stratum is substituted. The resulting open is allowed to be empty.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.SchemeFlatTargetOpen
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Target neighborhoods on which the complete original projection is flat. -/
def Patches := {U : Y.Opens // Flat (pullback.snd f U.ι)}

/-- The union retains the original scheme structure of the target. -/
def locus : Y.Opens := ⨆ U : Patches f, U.val

/-- Every actual flat neighborhood is retained. -/
theorem patch_le (U : Patches f) : U.val ≤ locus f := le_iSup _ U

/-- The flat neighborhoods cover their union without discarding source fibers. -/
def cover : (locus f).toScheme.OpenCover where
  I₀ := Patches f
  X U := U.val.toScheme
  f U := Y.homOfLE (patch_le f U)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    obtain ⟨U, hx⟩ := Opens.mem_iSup.mp x.property
    refine ⟨U, ⟨x.val, hx⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun a ↦ a ⟨x.val, hx⟩) (Y.homOfLE_ι (patch_le f U))

/-- The actual whole-source projection over the constructed open. -/
def projection : pullback f (locus f).ι ⟶ (locus f).toScheme := pullback.snd _ _

/-- Flatness is proved by target locality on the constructed cover. -/
instance projection_flat : Flat (projection f) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @Flat) (cover f)
  intro U
  change Flat (pullback.snd (projection f) ((cover f).f U))
  let h := (IsPullback.of_hasPullback (projection f) ((cover f).f U)).paste_horiz
    (IsPullback.of_hasPullback f (locus f).ι)
  have he : (cover f).f U ≫ (locus f).ι = U.val.ι :=
    Y.homOfLE_ι (patch_le f U)
  rw [he] at h
  have hp := h.isoPullback_hom_snd
  let _ := U.property
  rw [← hp]
  infer_instance

/-- Every smaller open inherits flatness of its complete inverse image. -/
theorem flat_of_le (U : Y.Opens) (hU : U ≤ locus f) : Flat (pullback.snd f U.ι) := by
  let i := Y.homOfLE hU
  let h := (IsPullback.of_hasPullback (projection f) i).paste_horiz
    (IsPullback.of_hasPullback f (locus f).ι)
  have he : i ≫ (locus f).ι = U.ι := Y.homOfLE_ι hU
  rw [he] at h
  have hp := h.isoPullback_inv_snd
  rw [← hp]
  infer_instance

/-- The constructed open exactly detects flatness on target neighborhoods. -/
theorem le_locus_iff (U : Y.Opens) : U ≤ locus f ↔ Flat (pullback.snd f U.ι) :=
  ⟨flat_of_le f U, fun h ↦ patch_le f ⟨U, h⟩⟩

/-- A globally flat original projection retains the whole target. -/
theorem locus_top [Flat f] : locus f = ⊤ :=
  top_le_iff.mp ((le_locus_iff f ⊤).mpr inferInstance)

end FLT.Mazur.SchemeFlatTargetOpen
