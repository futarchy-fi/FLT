/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSectionProjectiveChart
public import FLT.Mazur.WeierstrassIntegralProjectiveClosed

/-!
# Cubic-valued morphisms from normalized section coordinates

An actual normalized equation factors the section chart morphism through
the integral cubic over the original coefficient ring. The source open
need not be affine: its canonical map to its section spectrum suffices.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open WeierstrassIntegralChart ProjectiveSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} (M : X.Modules) {R : Type} [CommRing R]
  (W : WeierstrassCurve R) (t : Fin 3 → Γ(M, ⊤)) (j : Fin 3)
  (U : X.Opens) (hj : U ≤ sectionGeneratorOpen M (t j)) (r : R →+* Γ(X, U))
  (he : (W.map r).toProjective.Equation (fun i => sectionRatioOn M (t j) U hj (t i)))

/-- Evaluation on the genuine cubic chart by the actual normalized ratios. -/
def sectionCubicChartRingMap : Coordinate W j →+* Γ(X, U) :=
  letI := r.toAlgebra
  (evaluation W j (fun i => sectionRatioOn M (t j) U hj (t i)) he
    (sectionRatioOn_self M (t j) U hj)).toRingHom

/-- The cubic evaluation retains the actual ratio of each coordinate. -/
theorem sectionCubicChartRingMap_coordinate (i : Fin 3) :
    sectionCubicChartRingMap M W t j U hj r he (coord W j i) =
      sectionRatioOn M (t j) U hj (t i) := by
  let _ := r.toAlgebra
  exact evaluation_coord W j _ he _ i

/-- The factorization on coordinate rings is the original projective chart map. -/
theorem sectionCubicChartRingMap_projective :
    (sectionCubicChartRingMap M W t j U hj r he).comp
      (projectiveChartAlgebra W j).toRingHom =
        sectionProjectiveChartRingMap M 2 t j U hj r := by
  let _ := r.toAlgebra
  apply chartRing_hom_ext R (Fin 3) j
  · intro a
    exact (((evaluation W j _ he (sectionRatioOn_self M (t j) U hj)).comp
      (projectiveChartAlgebra W j)).commutes a).trans
        (sectionProjectiveChartRingMap_scalar M 2 t j U hj r a).symm
  · intro i
    change sectionCubicChartRingMap M W t j U hj r he
      (projectiveChartAlgebra W j (coordinate R (Fin 3) j i)) = _
    rw [projectiveChartAlgebra_coordinate, sectionCubicChartRingMap_coordinate,
      sectionProjectiveChartRingMap_coordinate]

/-- The regular morphism from the original generator open to the integral cubic. -/
def sectionCubicChartMorphism : U.toScheme ⟶ integralCurve W :=
  U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (U.topIso.inv.hom.comp (sectionCubicChartRingMap M W t j U hj r he))) ≫
      integralCurveChart W j

/-- The cubic-valued morphism has exactly the original projective-space image. -/
@[reassoc] theorem sectionCubicChartMorphism_projectiveMap :
    sectionCubicChartMorphism M W t j U hj r he ≫ integralProjectiveMap W =
      sectionProjectiveChartMorphism M 2 t j U hj r := by
  simp only [sectionCubicChartMorphism, Category.assoc,
    integralCurveChart_projectiveMap, projectiveChartMap, projectiveChartMorphism]
  rw [← Spec.map_comp_assoc]
  change U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((U.topIso.inv.hom.comp (sectionCubicChartRingMap M W t j U hj r he)).comp
      (projectiveChartAlgebra W j).toRingHom)) ≫ chartMap R (Fin 3) j = _
  rw [RingHom.comp_assoc, sectionCubicChartRingMap_projective]
  rfl

end FLT.Mazur.FCurve
