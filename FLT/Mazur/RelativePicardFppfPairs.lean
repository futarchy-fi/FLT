/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardPullbackSquares

/-!
# Original pair overlaps of a relative Picard covering family

The pair test scheme has its original fiber-product projections. Its total
space is canonically the overlap of the original total-space covering maps.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (T : Over S) (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left)

/-- The original pair overlap, regarded as a test scheme over the original base. -/
def relativeCoverPair (i j : 𝒰.I₀) : Over S :=
  Over.mk (Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ T.hom)

/-- The first original pair projection as a test-scheme map. -/
def relativeCoverPairLeft (i j : 𝒰.I₀) :
    relativeCoverPair T 𝒰 i j ⟶ relativeCoverMember T 𝒰 i :=
  Over.homMk (Limits.pullback.fst (𝒰.f i) (𝒰.f j))

/-- The second original pair projection as a test-scheme map. -/
def relativeCoverPairRight (i j : 𝒰.I₀) :
    relativeCoverPair T 𝒰 i j ⟶ relativeCoverMember T 𝒰 j :=
  Over.homMk (Limits.pullback.snd (𝒰.f i) (𝒰.f j)) (by
    change _ ≫ 𝒰.f j ≫ T.hom = _ ≫ 𝒰.f i ≫ T.hom
    rw [← Category.assoc, ← Category.assoc, Limits.pullback.condition])

/-- Both original projections have the same map to the covered test scheme. -/
theorem relativeCoverPair_condition (i j : 𝒰.I₀) :
    relativeCoverPairLeft T 𝒰 i j ≫ relativeCoverArrow T 𝒰 i =
      relativeCoverPairRight T 𝒰 i j ≫ relativeCoverArrow T 𝒰 j :=
  Over.OverMorphism.ext Limits.pullback.condition

/-- The base pair square is the original categorical pullback square. -/
theorem relativeCoverPair_isPullback (i j : 𝒰.I₀) :
    IsPullback (relativeCoverPairLeft T 𝒰 i j).left
      (relativeCoverPairRight T 𝒰 i j).left (relativeCoverArrow T 𝒰 i).left
      (relativeCoverArrow T 𝒰 j).left := IsPullback.of_hasPullback _ _

/-- Compare the actual pair total space with the overlap of the actual total cover. -/
def relativeCoverPairTotalIso (i j : 𝒰.I₀) :
    Limits.pullback f (relativeCoverPair T 𝒰 i j).hom ≅
      Limits.pullback ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j) :=
  relativeTotalOverlapIso f (relativeCoverPairLeft T 𝒰 i j)
    (relativeCoverPairRight T 𝒰 i j) (relativeCoverArrow T 𝒰 i) (relativeCoverArrow T 𝒰 j)
    (relativeCoverPair_isPullback T 𝒰 i j)

/-- The overlap comparison retains the first exact total-space projection. -/
@[reassoc]
theorem relativeCoverPairTotalIso_fst (i j : 𝒰.I₀) :
    (relativeCoverPairTotalIso f T 𝒰 i j).hom ≫ Limits.pullback.fst _ _ =
      relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) :=
  relativeTotalOverlapIso_fst _ _ _ _ _ _

/-- The overlap comparison retains the second exact total-space projection. -/
@[reassoc]
theorem relativeCoverPairTotalIso_snd (i j : 𝒰.I₀) :
    (relativeCoverPairTotalIso f T 𝒰 i j).hom ≫ Limits.pullback.snd _ _ =
      relativeTotalMap f (relativeCoverPairRight T 𝒰 i j) :=
  relativeTotalOverlapIso_snd _ _ _ _ _ _

/-- The inverse chart recovers the first original overlap projection. -/
@[reassoc]
theorem relativeCoverPairTotalIso_inv_fst (i j : 𝒰.I₀) :
    (relativeCoverPairTotalIso f T 𝒰 i j).inv ≫
        relativeTotalMap f (relativeCoverPairLeft T 𝒰 i j) =
      Limits.pullback.fst _ _ := by
  rw [← relativeCoverPairTotalIso_fst, Iso.inv_hom_id_assoc]

/-- The inverse chart recovers the second original overlap projection. -/
@[reassoc]
theorem relativeCoverPairTotalIso_inv_snd (i j : 𝒰.I₀) :
    (relativeCoverPairTotalIso f T 𝒰 i j).inv ≫
        relativeTotalMap f (relativeCoverPairRight T 𝒰 i j) =
      Limits.pullback.snd _ _ := by
  rw [← relativeCoverPairTotalIso_snd, Iso.inv_hom_id_assoc]

end FLT.Mazur.SchemePicard
