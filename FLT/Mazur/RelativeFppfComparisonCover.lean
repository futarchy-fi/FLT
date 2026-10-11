/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardFppfComparison
public import FLT.Mazur.RelativePicardFppfCover

/-!
# Actual covers for the relative Picard sheaf comparison

Covering sieves give small, jointly surjective fppf families with the original
relative test arrows. Neither representatives nor equality need a section
of the original family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.SchemePicard
universe u
variable {S : Scheme.{u}}

/-- Every covering sieve contains an actual small fppf family of test schemes. -/
theorem relativeFppf_exists_cover {T : Over S} (Z : Sieve T)
    (hZ : Z ∈ (Scheme.fppfTopology.over S) T) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left,
      ∀ i, Z (relativeCoverArrow T 𝒰 i) := by
  let _ : MorphismProperty.IsMultiplicative
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    { id_mem := fun _ ↦ inferInstance }
  rw [GrothendieckTopology.mem_over_iff] at hZ
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hZ
  exact ⟨𝒰, fun i ↦ (Sieve.overEquiv_iff Z (𝒰.f i)).mp (h𝒰 _ _ ⟨i⟩)⟩

variable {X : Scheme.{u}} (f : X ⟶ S)

/-- Every actual sheaf section has representatives on a jointly surjective fppf cover. -/
theorem relativeFppfClass_exists_cover (T : Over S)
    (s : (relativeFppfSheaf f).obj.obj (op T)) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left,
      ∀ i, ∃ c : RelativePic (Limits.pullback.snd f (relativeCoverMember T 𝒰 i).hom),
        relativeFppfClass f _ c = (relativeFppfSheaf f).obj.map
          (relativeCoverArrow T 𝒰 i).op s :=
  relativeFppf_exists_cover _ (relativeFppfClass_locallyRepresented f T s)

/-- Equality of represented sheaf sections is equality of classes on an actual fppf cover. -/
theorem relativeFppfClass_eq_exists_cover (T : Over S)
    (a b : RelativePic (Limits.pullback.snd f T.hom))
    (h : relativeFppfClass f T a = relativeFppfClass f T b) :
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left,
      ∀ i, relativeBaseMap f (relativeCoverArrow T 𝒰 i) a =
        relativeBaseMap f (relativeCoverArrow T 𝒰 i) b :=
  relativeFppf_exists_cover _ ((relativeFppfClass_eq_iff f T a b).mp h)

end FLT.Mazur.SchemePicard
