/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativePicardFppfPairs

/-!
# Original member diagonals and relative total-space charts

The base member diagonal is a map of test schemes. Its total-space map
is the actual cover diagonal followed by the inverse pair chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SchemePicard
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (T : Over S) (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left)

/-- The original diagonal of a member, as a map of test schemes. -/
def relativeCoverDiagonal (i : 𝒰.I₀) :
    relativeCoverMember T 𝒰 i ⟶ relativeCoverPair T 𝒰 i i :=
  Over.homMk (Limits.pullback.diagonal (𝒰.f i)) (by
    change _ ≫ Limits.pullback.fst _ _ ≫ 𝒰.f i ≫ T.hom = _
    rw [← Category.assoc, Limits.pullback.diagonal_fst, Category.id_comp]
    rfl)

/-- The first original projection retracts the member diagonal. -/
@[reassoc]
theorem relativeCoverDiagonal_left (i : 𝒰.I₀) :
    relativeCoverDiagonal T 𝒰 i ≫ relativeCoverPairLeft T 𝒰 i i =
      𝟙 (relativeCoverMember T 𝒰 i) :=
  Over.OverMorphism.ext (Limits.pullback.diagonal_fst _)

/-- The second original projection retracts the same member diagonal. -/
@[reassoc]
theorem relativeCoverDiagonal_right (i : 𝒰.I₀) :
    relativeCoverDiagonal T 𝒰 i ≫ relativeCoverPairRight T 𝒰 i i =
      𝟙 (relativeCoverMember T 𝒰 i) :=
  Over.OverMorphism.ext (Limits.pullback.diagonal_snd _)

/-- The first total-space projection retains the original retraction. -/
@[reassoc]
theorem relativeCoverDiagonal_total_left (i : 𝒰.I₀) :
    relativeTotalMap f (relativeCoverDiagonal T 𝒰 i) ≫
        relativeTotalMap f (relativeCoverPairLeft T 𝒰 i i) = 𝟙 _ := by
  rw [← relativeTotalMap_comp, relativeCoverDiagonal_left, relativeTotalMap_id]

/-- The second total-space projection retains the original retraction. -/
@[reassoc]
theorem relativeCoverDiagonal_total_right (i : 𝒰.I₀) :
    relativeTotalMap f (relativeCoverDiagonal T 𝒰 i) ≫
        relativeTotalMap f (relativeCoverPairRight T 𝒰 i i) = 𝟙 _ := by
  rw [← relativeTotalMap_comp, relativeCoverDiagonal_right, relativeTotalMap_id]

/-- The forward chart sends the original total-space diagonal to the actual cover diagonal. -/
theorem relativeCoverDiagonal_total_chart (i : 𝒰.I₀) :
    relativeTotalMap f (relativeCoverDiagonal T 𝒰 i) ≫
        (relativeCoverPairTotalIso f T 𝒰 i i).hom =
      Limits.pullback.diagonal ((relativeTotalCover f T 𝒰).f i) := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, relativeCoverPairTotalIso_fst,
      relativeCoverDiagonal_total_left, Limits.pullback.diagonal_fst]
  · rw [Category.assoc, relativeCoverPairTotalIso_snd,
      relativeCoverDiagonal_total_right, Limits.pullback.diagonal_snd]

/-- The inverse pair chart recovers exactly the original total-space diagonal. -/
theorem relativeCoverDiagonal_total_inverse (i : 𝒰.I₀) :
    Limits.pullback.diagonal ((relativeTotalCover f T 𝒰).f i) ≫
        (relativeCoverPairTotalIso f T 𝒰 i i).inv =
      relativeTotalMap f (relativeCoverDiagonal T 𝒰 i) := by
  rw [← relativeCoverDiagonal_total_chart, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

end FLT.Mazur.SchemePicard
