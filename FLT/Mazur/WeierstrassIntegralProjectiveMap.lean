/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectiveChartAlgebra
public import FLT.Mazur.WeierstrassIntegralCurveMorphisms
public import FLT.Mazur.ProjectiveChartMapCompatibility

/-!
# The integral cubic's actual morphism to projective space

The surjective ambient-chart algebras give local scheme maps. The explicit
normalization transitions make them agree on overlaps, hence descend to the
glued integral cubic over its original coefficient spectrum.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The normalized cubic chart maps into its matching projective affine chart. -/
def projectiveChartMorphism (j : Fin 3) :
    chartScheme W j ⟶ Spec (.of (ProjectiveSpace.chartRing R (Fin 3) j)) :=
  Spec.map (CommRingCat.ofHom (projectiveChartAlgebra W j).toRingHom)

/-- The local ambient morphism on each chart of the integral cubic. -/
def projectiveChartMap (j : Fin 3) : chartScheme W j ⟶ ProjectiveSpace.space R (Fin 3) :=
  projectiveChartMorphism W j ≫ ProjectiveSpace.chartMap R (Fin 3) j

/-- Integral normalization agrees with the projective ambient transition. -/
theorem projectiveChartMap_compatibility (j k : Fin 3) :
    overlapInclusion W j k ≫ projectiveChartMap W j =
      chartTransition W j k ≫ overlapInclusion W k j ≫ projectiveChartMap W k := by
  let f := (overlapRestriction W j k).comp (projectiveChartAlgebra W j)
  let g := ((transition W j k).comp (overlapRestriction W k j)).comp
    (projectiveChartAlgebra W k)
  have he := ProjectiveSpace.chartMaps_eq_of_coordinates R (Overlap W j k) (Fin 3)
    j k f.toRingHom g.toRingHom (fun a => (f.commutes a).trans (g.commutes a).symm)
    (fun i => by
      change overlapRestriction W j k
        (projectiveChartAlgebra W j (ProjectiveSpace.coordinate R (Fin 3) j i)) =
        transition W j k (overlapRestriction W k j
          (projectiveChartAlgebra W k (ProjectiveSpace.coordinate R (Fin 3) k i))) *
        overlapRestriction W j k
          (projectiveChartAlgebra W j (ProjectiveSpace.coordinate R (Fin 3) j k))
      simp only [projectiveChartAlgebra_coordinate]
      change overlapCoord W j k i = transition W j k (overlapCoord W k j i) *
        overlapCoord W j k k
      rw [transition_coord, mul_right_comm, overlapInverse_mul, one_mul])
    (by
      change IsUnit (overlapRestriction W j k
        (projectiveChartAlgebra W j (ProjectiveSpace.coordinate R (Fin 3) j k)))
      rw [projectiveChartAlgebra_coordinate]
      exact overlapCoord_isUnit W j k)
  convert he using 1 <;>
    simp only [projectiveChartMap, projectiveChartMorphism, overlapInclusion,
      chartTransition, PrincipalAffineRefinement.inclusion, ← Spec.map_comp_assoc]
  · congr 2
  · congr 2

/-- The actual integral cubic morphism to projective two-space. -/
def integralProjectiveMap : integralCurve W ⟶ ProjectiveSpace.space R (Fin 3) :=
  integralCurveDesc W (projectiveChartMap W) (projectiveChartMap_compatibility W)

/-- The global projective morphism recovers the concrete map on every chart. -/
@[reassoc] theorem integralCurveChart_projectiveMap (j : Fin 3) :
    integralCurveChart W j ≫ integralProjectiveMap W = projectiveChartMap W j :=
  integralCurveChart_desc W _ _ j

/-- Each local map respects the coefficient spectrum. -/
@[reassoc] theorem projectiveChartMap_baseProjection (j : Fin 3) :
    projectiveChartMap W j ≫ ProjectiveSpace.baseProjection R (Fin 3) =
      chartStructure W j := by
  rw [projectiveChartMap, Category.assoc, ProjectiveSpace.chartMap_baseProjection]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (projectiveChartAlgebra W j).commutes

/-- The descended projective morphism lies over the original base ring. -/
@[reassoc] theorem integralProjectiveMap_baseProjection :
    integralProjectiveMap W ≫ ProjectiveSpace.baseProjection R (Fin 3) =
      integralCurveStructure W := by
  apply integralCurve_hom_ext
  intro j
  rw [← Category.assoc, integralCurveChart_projectiveMap,
    projectiveChartMap_baseProjection, integralCurveChart_structure]

end FLT.Mazur.WeierstrassIntegralChart
