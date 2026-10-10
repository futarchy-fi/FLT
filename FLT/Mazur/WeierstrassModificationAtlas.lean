/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYOpenImmersion

/-!
# The actual three-chart atlas of the glued modification

The x-direction, divided, and y-direction equation spectra form an open atlas
of the same constructed modification. The third chart is exactly the union
of the two open pieces already identified inside the original two charts.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The three original equation spectra, in x, divided, y order. -/
def atlasObject (i : Fin 3) : Scheme :=
  ![Spec (.of (WeierstrassModificationX.Coordinate W s b3 b4 b6)),
    Spec (.of (WeierstrassDilatation.Coordinate W s b3 b4 b6)),
    Spec (.of (Coordinate W s b3 b4 b6))] i

/-- Their actual maps to the constructed two-chart modification. -/
def atlasMap (i : Fin 3) : atlasObject W s b3 b4 b6 i ⟶
    WeierstrassModificationX.modification W s b3 b4 b6 := by
  refine Fin.cases (WeierstrassModificationX.xChart W s b3 b4 b6) ?_ i
  intro j
  refine Fin.cases (WeierstrassModificationX.dividedChart W s b3 b4 b6) ?_ j
  intro k
  exact Fin.cases (yChart W s b3 b4 b6) (fun l => Fin.elim0 l) k

/-- All three actual chart maps are open immersions. -/
instance atlasMap_isOpenImmersion (i : Fin 3) : IsOpenImmersion (atlasMap W s b3 b4 b6 i) := by
  fin_cases i
  · exact WeierstrassModificationX.xChart_isOpenImmersion W s b3 b4 b6
  · exact WeierstrassModificationX.dividedChart_isOpenImmersion W s b3 b4 b6
  · exact yChart_isOpenImmersion W s b3 b4 b6

/-- The original three equations are an open atlas of the constructed modification. -/
def threeChartAtlas : (WeierstrassModificationX.modification W s b3 b4 b6).OpenCover where
  I₀ := Fin 3
  X := atlasObject W s b3 b4 b6
  f := atlasMap W s b3 b4 b6
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun i => atlasMap_isOpenImmersion W s b3 b4 b6 i⟩
    intro z
    rcases WeierstrassModificationX.modification_charts_cover W s b3 b4 b6 z with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

/-- The y-direction image is exactly the union of its two existing open pieces. -/
theorem yChart_range : Set.range (yChart W s b3 b4 b6) =
    Set.range (scaleToModification W s b3 b4 b6) ∪
      Set.range (horizontalToModification W s b3 b4 b6) := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    rcases ratio_points_cover W s b3 b4 b6 p with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · left
      refine ⟨q, ?_⟩
      exact congrArg (fun f => f q) (scale_yChart W s b3 b4 b6).symm
    · right
      refine ⟨q, ?_⟩
      exact congrArg (fun f => f q) (horizontal_yChart W s b3 b4 b6).symm
  · rintro (⟨q, rfl⟩ | ⟨q, rfl⟩)
    · exact ⟨PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0) q,
        congrArg (fun f => f q) (scale_yChart W s b3 b4 b6)⟩
    · exact ⟨PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1) q,
        congrArg (fun f => f q) (horizontal_yChart W s b3 b4 b6)⟩

/-- The same identification as an equality of open subschemes. -/
theorem yChart_opensRange : (yChart W s b3 b4 b6).opensRange =
    (scaleToModification W s b3 b4 b6).opensRange ⊔
      (horizontalToModification W s b3 b4 b6).opensRange :=
  TopologicalSpace.Opens.ext (yChart_range W s b3 b4 b6)

/-- Each member of the atlas retains its original cubic contraction. -/
theorem atlasMap_contraction (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4)
    (h6 : W.a₆ = s ^ 2 * b6) :
    (atlasMap W s b3 b4 b6 0 ≫ WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6 =
      WeierstrassModificationX.toCurve W s b3 b4 b6 h3 h4 h6) ∧
    (atlasMap W s b3 b4 b6 1 ≫ WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6 =
      WeierstrassDilatation.toCurve W s b3 b4 b6 h3 h4 h6) ∧
    (atlasMap W s b3 b4 b6 2 ≫ WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6 =
      toCurve W s b3 b4 b6 h3 h4 h6) :=
  ⟨WeierstrassModificationX.xChart_contraction W s b3 b4 b6 h3 h4 h6,
    WeierstrassModificationX.dividedChart_contraction W s b3 b4 b6 h3 h4 h6,
    yChart_contraction W s b3 b4 b6 h3 h4 h6⟩

end FLT.Mazur.WeierstrassModificationY
