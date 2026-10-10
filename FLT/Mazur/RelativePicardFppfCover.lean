/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedPicardBaseChange
public import FLT.Mazur.SchemeFppfFamilyCover

/-!
# Fppf covers on the actual relative Picard total spaces

A cover of a test scheme induces a cover whose members are exactly the
fiber products used by the Picard presheaf. Its arrows are the original
relative total-space maps, rather than isomorphic substitute schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Each restriction square of the actual total spaces is cartesian. -/
theorem relativeTotalMap_isPullback {T U : Over S} (g : T ⟶ U) :
    IsPullback (relativeTotalMap f g) (Limits.pullback.snd f T.hom)
      (Limits.pullback.snd f U.hom) g.left := by
  apply IsPullback.of_right _ (relativeTotalMap_snd f g)
    (IsPullback.of_hasPullback f U.hom)
  simpa only [relativeTotalMap_fst, Over.w] using IsPullback.of_hasPullback f T.hom

/-- The canonical comparison with base change along a test-scheme map. -/
def relativeTotalBaseChangeIso {T U : Over S} (g : T ⟶ U) :
    Limits.pullback f T.hom ≅ Limits.pullback (Limits.pullback.snd f U.hom) g.left :=
  (relativeTotalMap_isPullback f g).isoPullback

/-- The base-change comparison preserves the original total-space restriction. -/
@[reassoc]
theorem relativeTotalBaseChangeIso_fst {T U : Over S} (g : T ⟶ U) :
    (relativeTotalBaseChangeIso f g).hom ≫ Limits.pullback.fst _ _ =
      relativeTotalMap f g := (relativeTotalMap_isPullback f g).isoPullback_hom_fst

variable (T : Over S) (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left)

/-- An original covering member as a test scheme over the original base. -/
def relativeCoverMember (i : 𝒰.I₀) : Over S := Over.mk (𝒰.f i ≫ T.hom)

/-- The original covering arrow regarded as a map of test schemes. -/
def relativeCoverArrow (i : 𝒰.I₀) : relativeCoverMember T 𝒰 i ⟶ T :=
  Over.homMk (𝒰.f i)

/-- The fppf cover consists of the original Picard total spaces and restriction maps. -/
def relativeTotalCover : Scheme.Cover.{u} Scheme.fppfPrecoverage
    (Limits.pullback f T.hom) :=
  Scheme.Cover.copy (𝒰.pullback₁ (Limits.pullback.snd f T.hom)) 𝒰.I₀
    (fun i ↦ Limits.pullback f (relativeCoverMember T 𝒰 i).hom)
    (fun i ↦ relativeTotalMap f (relativeCoverArrow T 𝒰 i)) (Equiv.refl _)
    (fun i ↦ relativeTotalBaseChangeIso f (relativeCoverArrow T 𝒰 i))
    (fun i ↦ (relativeTotalBaseChangeIso_fst f (relativeCoverArrow T 𝒰 i)).symm)

/-- The induced cover retains each exact total-space object. -/
theorem relativeTotalCover_obj (i : 𝒰.I₀) :
    (relativeTotalCover f T 𝒰).X i =
      Limits.pullback f (relativeCoverMember T 𝒰 i).hom := rfl

/-- The induced cover retains each exact presheaf restriction arrow. -/
theorem relativeTotalCover_map (i : 𝒰.I₀) :
    (relativeTotalCover f T 𝒰).f i = relativeTotalMap f (relativeCoverArrow T 𝒰 i) := rfl

end FLT.Mazur.SchemePicard
