/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardFppfPairs
public import FLT.Mazur.SchemeFamilyTripleOverlap

/-!
# Original triple overlaps as relative Picard test schemes

The adjacent-pair triple retains all original pair maps and three named
member coordinates. Its middle coordinate is shared by the adjacent pairs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
open SchemeFamilyTripleOverlap
variable {S : Scheme.{u}} (T : Over S)
  (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left)

/-- The actual adjacent-pair triple, regarded as a test scheme over the base. -/
def relativeCoverTriple (i j k : 𝒰.I₀) : Over S :=
  Over.mk (coord1 (𝒰.f i) (𝒰.f j) (𝒰.f k) ≫ 𝒰.f i ≫ T.hom)

/-- The original first adjacent pair map. -/
def relativeCoverTriple12 (i j k : 𝒰.I₀) :
    relativeCoverTriple T 𝒰 i j k ⟶ relativeCoverPair T 𝒰 i j :=
  Over.homMk (pair12 (𝒰.f i) (𝒰.f j) (𝒰.f k)) (by
    simp only [relativeCoverPair, relativeCoverTriple, Over.mk_left, Over.mk_hom,
      coord1, Category.assoc])

/-- The original second adjacent pair map. -/
def relativeCoverTriple23 (i j k : 𝒰.I₀) :
    relativeCoverTriple T 𝒰 i j k ⟶ relativeCoverPair T 𝒰 j k :=
  Over.homMk (pair23 (𝒰.f i) (𝒰.f j) (𝒰.f k)) (by
    change _ ≫ Limits.pullback.fst _ _ ≫ 𝒰.f j ≫ T.hom =
      (pair12 _ _ _ ≫ Limits.pullback.fst _ _) ≫ 𝒰.f i ≫ T.hom
    rw [← Category.assoc, pair23_fst]
    simpa only [coord2, Category.assoc] using
      congrArg (fun q ↦ pair12 (𝒰.f i) (𝒰.f j) (𝒰.f k) ≫ q ≫ T.hom)
        (Limits.pullback.condition (f := 𝒰.f i) (g := 𝒰.f j)).symm)

/-- The original outer pair map. -/
def relativeCoverTriple13 (i j k : 𝒰.I₀) :
    relativeCoverTriple T 𝒰 i j k ⟶ relativeCoverPair T 𝒰 i k :=
  Over.homMk (pair13 (𝒰.f i) (𝒰.f j) (𝒰.f k)) (by
    change _ ≫ Limits.pullback.fst _ _ ≫ 𝒰.f i ≫ T.hom = _
    rw [← Category.assoc, pair13_fst]
    rfl)

/-- The named first coordinate retains the original pair projection. -/
def relativeCoverTripleFirst (i j k : 𝒰.I₀) :
    relativeCoverTriple T 𝒰 i j k ⟶ relativeCoverMember T 𝒰 i :=
  relativeCoverTriple12 T 𝒰 i j k ≫ relativeCoverPairLeft T 𝒰 i j

/-- The named common middle coordinate. -/
def relativeCoverTripleMiddle (i j k : 𝒰.I₀) :
    relativeCoverTriple T 𝒰 i j k ⟶ relativeCoverMember T 𝒰 j :=
  relativeCoverTriple12 T 𝒰 i j k ≫ relativeCoverPairRight T 𝒰 i j

/-- The named last coordinate retains the second adjacent pair projection. -/
def relativeCoverTripleLast (i j k : 𝒰.I₀) :
    relativeCoverTriple T 𝒰 i j k ⟶ relativeCoverMember T 𝒰 k :=
  relativeCoverTriple23 T 𝒰 i j k ≫ relativeCoverPairRight T 𝒰 j k

/-- Both adjacent pair maps give exactly the same named middle test-scheme map. -/
@[reassoc]
theorem relativeCoverTriple23_left (i j k : 𝒰.I₀) :
    relativeCoverTriple23 T 𝒰 i j k ≫ relativeCoverPairLeft T 𝒰 j k =
      relativeCoverTripleMiddle T 𝒰 i j k :=
  Over.OverMorphism.ext (pair23_fst _ _ _)

/-- The outer pair retains the named first coordinate. -/
@[reassoc]
theorem relativeCoverTriple13_left (i j k : 𝒰.I₀) :
    relativeCoverTriple13 T 𝒰 i j k ≫ relativeCoverPairLeft T 𝒰 i k =
      relativeCoverTripleFirst T 𝒰 i j k :=
  Over.OverMorphism.ext (pair13_fst _ _ _)

/-- The outer pair retains the named last coordinate. -/
@[reassoc]
theorem relativeCoverTriple13_right (i j k : 𝒰.I₀) :
    relativeCoverTriple13 T 𝒰 i j k ≫ relativeCoverPairRight T 𝒰 i k =
      relativeCoverTripleLast T 𝒰 i j k :=
  Over.OverMorphism.ext (pair13_snd _ _ _)

/-- The adjacent-pair square is the original categorical pullback square. -/
theorem relativeCoverTriple_isPullback (i j k : 𝒰.I₀) :
    IsPullback (relativeCoverTriple12 T 𝒰 i j k).left
      (relativeCoverTriple23 T 𝒰 i j k).left
      (relativeCoverPairRight T 𝒰 i j).left
      (relativeCoverPairLeft T 𝒰 j k).left := IsPullback.of_hasPullback _ _

end FLT.Mazur.SchemePicard
