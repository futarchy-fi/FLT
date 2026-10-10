/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardTripleTotalChart

/-!
# Coordinates retained by the actual relative triple chart

The forward and inverse charts retain all three member coordinates and all
three pair maps, including the outer pair needed by the unequal cocycle.
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

/-- The triple chart retains original member coordinate 1. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_coord1 (i j k : 𝒰.I₀) :
    (relativeCoverTripleTotalIso f T 𝒰 i j k).hom ≫
        coord1 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
          ((relativeTotalCover f T 𝒰).f k) =
      relativeTotalMap f (relativeCoverTripleFirst T 𝒰 i j k) := by
  rw [coord1, ← Category.assoc, relativeCoverTripleTotalIso_pair12,
    Category.assoc, relativeCoverPairTotalIso_fst, ← relativeTotalMap_comp]
  rfl

/-- The triple chart retains original member coordinate 2. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_coord2 (i j k : 𝒰.I₀) :
    (relativeCoverTripleTotalIso f T 𝒰 i j k).hom ≫
        coord2 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
          ((relativeTotalCover f T 𝒰).f k) =
      relativeTotalMap f (relativeCoverTripleMiddle T 𝒰 i j k) := by
  rw [coord2, ← Category.assoc, relativeCoverTripleTotalIso_pair12,
    Category.assoc, relativeCoverPairTotalIso_snd, ← relativeTotalMap_comp]
  rfl

/-- The triple chart retains original member coordinate 3. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_coord3 (i j k : 𝒰.I₀) :
    (relativeCoverTripleTotalIso f T 𝒰 i j k).hom ≫
        coord3 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
          ((relativeTotalCover f T 𝒰).f k) =
      relativeTotalMap f (relativeCoverTripleLast T 𝒰 i j k) := by
  rw [coord3, ← Category.assoc, relativeCoverTripleTotalIso_pair23,
    Category.assoc, relativeCoverPairTotalIso_snd, ← relativeTotalMap_comp]
  rfl

/-- The triple chart also retains the original outer pair map. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_pair13 (i j k : 𝒰.I₀) :
    (relativeCoverTripleTotalIso f T 𝒰 i j k).hom ≫
        pair13 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
          ((relativeTotalCover f T 𝒰).f k) =
      relativeTotalMap f (relativeCoverTriple13 T 𝒰 i j k) ≫
        (relativeCoverPairTotalIso f T 𝒰 i k).hom := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, pair13_fst, relativeCoverTripleTotalIso_coord1,
      Category.assoc, relativeCoverPairTotalIso_fst, ← relativeTotalMap_comp,
      relativeCoverTriple13_left]
  · rw [Category.assoc, pair13_snd, relativeCoverTripleTotalIso_coord3,
      Category.assoc, relativeCoverPairTotalIso_snd, ← relativeTotalMap_comp,
      relativeCoverTriple13_right]

/-- The inverse triple chart recovers exact member coordinate 1. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_inv_coord1 (i j k : 𝒰.I₀) :
    (relativeCoverTripleTotalIso f T 𝒰 i j k).inv ≫
        relativeTotalMap f (relativeCoverTripleFirst T 𝒰 i j k) =
      coord1 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
        ((relativeTotalCover f T 𝒰).f k) := by
  rw [← relativeCoverTripleTotalIso_coord1, Iso.inv_hom_id_assoc]

/-- The inverse triple chart recovers exact member coordinate 2. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_inv_coord2 (i j k : 𝒰.I₀) :
    (relativeCoverTripleTotalIso f T 𝒰 i j k).inv ≫
        relativeTotalMap f (relativeCoverTripleMiddle T 𝒰 i j k) =
      coord2 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
        ((relativeTotalCover f T 𝒰).f k) := by
  rw [← relativeCoverTripleTotalIso_coord2, Iso.inv_hom_id_assoc]

/-- The inverse triple chart recovers exact member coordinate 3. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_inv_coord3 (i j k : 𝒰.I₀) :
    (relativeCoverTripleTotalIso f T 𝒰 i j k).inv ≫
        relativeTotalMap f (relativeCoverTripleLast T 𝒰 i j k) =
      coord3 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
        ((relativeTotalCover f T 𝒰).f k) := by
  rw [← relativeCoverTripleTotalIso_coord3, Iso.inv_hom_id_assoc]

/-- The inverse triple chart recovers the exact pair 12 chart. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_inv_pair12 (i j k : 𝒰.I₀) :
    pair12 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
        ((relativeTotalCover f T 𝒰).f k) ≫ (relativeCoverPairTotalIso f T 𝒰 i j).inv =
      (relativeCoverTripleTotalIso f T 𝒰 i j k).inv ≫
        relativeTotalMap f (relativeCoverTriple12 T 𝒰 i j k) := by
  apply (cancel_epi (relativeCoverTripleTotalIso f T 𝒰 i j k).hom).mp
  rw [← Category.assoc, relativeCoverTripleTotalIso_pair12,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- The inverse triple chart recovers the exact pair 23 chart. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_inv_pair23 (i j k : 𝒰.I₀) :
    pair23 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
        ((relativeTotalCover f T 𝒰).f k) ≫ (relativeCoverPairTotalIso f T 𝒰 j k).inv =
      (relativeCoverTripleTotalIso f T 𝒰 i j k).inv ≫
        relativeTotalMap f (relativeCoverTriple23 T 𝒰 i j k) := by
  apply (cancel_epi (relativeCoverTripleTotalIso f T 𝒰 i j k).hom).mp
  rw [← Category.assoc, relativeCoverTripleTotalIso_pair23,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- The inverse triple chart recovers the exact pair 13 chart. -/
@[reassoc]
theorem relativeCoverTripleTotalIso_inv_pair13 (i j k : 𝒰.I₀) :
    pair13 ((relativeTotalCover f T 𝒰).f i) ((relativeTotalCover f T 𝒰).f j)
        ((relativeTotalCover f T 𝒰).f k) ≫ (relativeCoverPairTotalIso f T 𝒰 i k).inv =
      (relativeCoverTripleTotalIso f T 𝒰 i j k).inv ≫
        relativeTotalMap f (relativeCoverTriple13 T 𝒰 i j k) := by
  apply (cancel_epi (relativeCoverTripleTotalIso f T 𝒰 i j k).hom).mp
  rw [← Category.assoc, relativeCoverTripleTotalIso_pair13,
    Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

end FLT.Mazur.SchemePicard
