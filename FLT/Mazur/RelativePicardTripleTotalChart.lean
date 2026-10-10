/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardCoverTriples

/-!
# The actual total-space chart of an unequal triple

The total space of the original base triple is the triple overlap of the
actual total cover. Both adjacent pair charts are retained by this comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open SchemeFamilyTripleOverlap
variable {X S : Scheme.{u}} (f : X ⟶ S)
  (T : Over S) (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left)

/-- The original triple total space is cartesian over the actual adjacent total pairs. -/
theorem relativeCoverTriple_total_isPullback (i j k : 𝒰.I₀) :
    IsPullback
      (relativeTotalMap f (relativeCoverTriple12 T 𝒰 i j k) ≫
        (relativeCoverPairTotalIso f T 𝒰 i j).hom)
      (relativeTotalMap f (relativeCoverTriple23 T 𝒰 i j k) ≫
        (relativeCoverPairTotalIso f T 𝒰 j k).hom)
      (Limits.pullback.snd ((relativeTotalCover f T 𝒰).f i)
        ((relativeTotalCover f T 𝒰).f j))
      (Limits.pullback.fst ((relativeTotalCover f T 𝒰).f j)
        ((relativeTotalCover f T 𝒰).f k)) := by
  apply (relativeTotalMap_square_isPullback f
    (relativeCoverTriple12 T 𝒰 i j k) (relativeCoverTriple23 T 𝒰 i j k)
    (relativeCoverPairRight T 𝒰 i j) (relativeCoverPairLeft T 𝒰 j k)
    (relativeCoverTriple_isPullback T 𝒰 i j k)).of_iso
    (Iso.refl _) (relativeCoverPairTotalIso f T 𝒰 i j)
    (relativeCoverPairTotalIso f T 𝒰 j k) (Iso.refl _)
  · exact (Category.id_comp _).symm
  · exact (Category.id_comp _).symm
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (relativeCoverPairTotalIso_snd f T 𝒰 i j).symm
  · simpa only [Iso.refl_hom, Category.comp_id] using
      (relativeCoverPairTotalIso_fst f T 𝒰 j k).symm

/-- The prescribed comparison with the original triple of actual total-cover arrows. -/
def relativeCoverTripleTotalIso (i j k : 𝒰.I₀) :
    Limits.pullback f (relativeCoverTriple T 𝒰 i j k).hom ≅
      triple ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
        ((relativeTotalCover f T 𝒰).f k) :=
  (relativeCoverTriple_total_isPullback f T 𝒰 i j k).isoPullback

/-- The triple chart preserves the original first adjacent pair. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_pair12 (i j k : 𝒰.I₀) :
    (relativeCoverTripleTotalIso f T 𝒰 i j k).hom ≫
        pair12 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
          ((relativeTotalCover f T 𝒰).f k) =
      relativeTotalMap f (relativeCoverTriple12 T 𝒰 i j k) ≫
        (relativeCoverPairTotalIso f T 𝒰 i j).hom :=
  (relativeCoverTriple_total_isPullback f T 𝒰 i j k).isoPullback_hom_fst

/-- The triple chart preserves the original second adjacent pair. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_pair23 (i j k : 𝒰.I₀) :
    (relativeCoverTripleTotalIso f T 𝒰 i j k).hom ≫
        pair23 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
          ((relativeTotalCover f T 𝒰).f k) =
      relativeTotalMap f (relativeCoverTriple23 T 𝒰 i j k) ≫
        (relativeCoverPairTotalIso f T 𝒰 j k).hom :=
  (relativeCoverTriple_total_isPullback f T 𝒰 i j k).isoPullback_hom_snd

end FLT.Mazur.SchemePicard
