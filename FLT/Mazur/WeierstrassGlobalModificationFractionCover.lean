/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGlobalModificationGluing
public import FLT.Mazur.WeierstrassModificationReesProjIso
public import FLT.Mazur.WeierstrassFractionSmoothPresentation

/-!
# Original fraction charts and infinity cover the whole modification

Transport the three entire original Rees charts through the proved Proj
isomorphism and adjoin the unchanged original infinity chart. This gives
an actual affine cover, including all exceptional and infinity points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassGlobalModification

open WeierstrassIntegralChart WeierstrassModificationReesCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) (hs : s ≠ 0)

/-- The ring of an original input chart; `none` is the unchanged infinity chart. -/
def originalFractionCoverRing : Option (Fin 3) → CommRingCat
  | none => .of (Coordinate W 1)
  | some i => .of (BlowupFractionChart.chart (modificationChartCenter W s 2)
      (centerGenerators W s i))

/-- The original fraction input maps, with the entire infinity chart added. -/
def originalFractionCoverMap (i : Option (Fin 3)) :
    Spec (originalFractionCoverRing W s i) ⟶ model W s b3 b4 b6 h3 h4 h6 hs :=
  match i with
  | none => infinityChart W s b3 b4 b6 h3 h4 h6 hs
  | some j => BlowupRees.fractionChartInclusion (modificationChartCenter W s 2)
      (centerGenerators W s j) (centerGenerators_mem W s j) ≫
        (modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).inv ≫
          localChart W s b3 b4 b6 h3 h4 h6 hs

instance originalFractionCoverMap_isOpenImmersion (i : Option (Fin 3)) :
    IsOpenImmersion (originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs i) := by
  cases i <;> unfold originalFractionCoverMap <;> infer_instance

/-- Every original fraction input contracts by its original coordinate map. -/
@[reassoc] theorem originalFractionCoverMap_some_contraction (i : Fin 3) :
    originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs (some i) ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs =
      fractionSmoothContraction W s (centerGenerators W s i) := by
  simp only [originalFractionCoverMap, Category.assoc, localChart_contraction,
    modificationProjIso_inv_contraction]
  exact BlowupRees.fractionChartInclusion_contraction_assoc
    (modificationChartCenter W s 2) (centerGenerators W s i)
    (centerGenerators_mem W s i) (integralCurveChart W 2)

/-- The infinity member retains precisely its original projective chart map. -/
@[reassoc] theorem originalFractionCoverMap_none_contraction :
    originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs none ≫
        contraction W s b3 b4 b6 h3 h4 h6 hs = integralCurveChart W 1 :=
  infinityChart_contraction W s b3 b4 b6 h3 h4 h6 hs

/-- The entire original fraction charts and infinity together reach every modified point. -/
theorem originalFractionCoverMap_covers (z : model W s b3 b4 b6 h3 h4 h6 hs) :
    ∃ (i : Option (Fin 3)) (x : Spec (originalFractionCoverRing W s i)),
      originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs i x = z := by
  rcases charts_cover W s b3 b4 b6 h3 h4 h6 hs z with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact ⟨none, x, hx⟩
  · obtain ⟨i, a, ha⟩ := (originalProjCover W s).exists_eq
      ((modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).hom x)
    refine ⟨some i, a, ?_⟩
    change localChart W s b3 b4 b6 h3 h4 h6 hs
      ((modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).inv
        ((originalProjCover W s).f i a)) = z
    rw [ha]
    have he : (modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).inv
        ((modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).hom x) = x :=
      congrArg (fun t : WeierstrassModificationX.modification W s b3 b4 b6 ⟶
        WeierstrassModificationX.modification W s b3 b4 b6 => t x)
          (modificationProjIso W s b3 b4 b6 h3 h4 h6 hs).hom_inv_id
    rw [he, hx]

/-- The complete affine input cover of the whole single-step projective modification. -/
def originalFractionCover : (model W s b3 b4 b6 h3 h4 h6 hs).AffineOpenCover where
  I₀ := Option (Fin 3)
  X := originalFractionCoverRing W s
  f := originalFractionCoverMap W s b3 b4 b6 h3 h4 h6 hs
  idx z := (originalFractionCoverMap_covers W s b3 b4 b6 h3 h4 h6 hs z).choose
  covers z := (originalFractionCoverMap_covers W s b3 b4 b6 h3 h4 h6 hs z).choose_spec

end FLT.Mazur.WeierstrassGlobalModification
