/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralProjectivePreimage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The integral cubic is closed in projective two-space

The inverse-image computation identifies the restriction over each projective
chart with the surjective ambient-chart algebra. Closed immersion then descends
along the standard projective cover, over every commutative coefficient ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (j : Fin 3)

/-- The affine ambient morphism is closed because its ring map is surjective. -/
instance projectiveChartMorphism_closedImmersion :
    IsClosedImmersion (projectiveChartMorphism W j) :=
  IsClosedImmersion.spec_of_surjective _ (projectiveChartAlgebra_surjective W j)

/-- The normalized cubic chart maps to the actual open subscheme of projective space. -/
def projectiveChartToOpen : chartScheme W j ⟶ (ProjectiveSpace.chart R (Fin 3) j).toScheme :=
  projectiveChartMorphism W j ≫ (ProjectiveSpace.chartIso R (Fin 3) j).inv

/-- The square of actual open chart inclusions is cartesian. -/
theorem integralProjectiveChart_isPullback :
    IsPullback (projectiveChartToOpen W j) (integralCurveChart W j)
      (ProjectiveSpace.chart R (Fin 3) j).ι (integralProjectiveMap W) := by
  apply IsOpenImmersion.isPullback
  · exact integralCurveChart_projectiveMap W j
  · rw [Scheme.Opens.opensRange_ι, integralProjectiveMap_preimage_chart]

/-- The inverse image of a projective chart is the original normalized cubic scheme. -/
def integralProjectiveRestrictIso : chartScheme W j ≅
    (integralProjectiveMap W ⁻¹ᵁ ProjectiveSpace.chart R (Fin 3) j).toScheme :=
  (integralProjectiveChart_isPullback W j).isoIsPullback _ _
    (isPullback_morphismRestrict (integralProjectiveMap W) (ProjectiveSpace.chart R (Fin 3) j))

/-- The restriction is the actual ambient chart quotient, under the constructed comparison. -/
@[reassoc] theorem integralProjectiveRestrictIso_hom_restrict :
    (integralProjectiveRestrictIso W j).hom ≫
        (integralProjectiveMap W ∣_ ProjectiveSpace.chart R (Fin 3) j) =
      projectiveChartToOpen W j :=
  (integralProjectiveChart_isPullback W j).isoIsPullback_hom_fst _ _ _

/-- The comparison retains the original inclusion of the cubic chart. -/
@[reassoc] theorem integralProjectiveRestrictIso_hom_ι :
    (integralProjectiveRestrictIso W j).hom ≫
        (integralProjectiveMap W ⁻¹ᵁ ProjectiveSpace.chart R (Fin 3) j).ι =
      integralCurveChart W j :=
  (integralProjectiveChart_isPullback W j).isoIsPullback_hom_snd _ _ _

/-- Each restriction of the global projective map is a closed immersion. -/
instance integralProjectiveMap_restrict_closedImmersion :
    IsClosedImmersion (integralProjectiveMap W ∣_ ProjectiveSpace.chart R (Fin 3) j) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
    (integralProjectiveRestrictIso W j).hom, integralProjectiveRestrictIso_hom_restrict]
  dsimp only [projectiveChartToOpen]
  infer_instance

/-- The actual integral cubic is a closed subscheme of projective two-space. -/
instance integralProjectiveMap_closedImmersion : IsClosedImmersion (integralProjectiveMap W) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (ProjectiveSpace.chart R (Fin 3)) (ProjectiveSpace.iSup_chart R (Fin 3))
  intro j
  exact integralProjectiveMap_restrict_closedImmersion W j

end FLT.Mazur.WeierstrassIntegralChart
