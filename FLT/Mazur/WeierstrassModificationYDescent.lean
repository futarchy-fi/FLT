/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationYCompatibility

/-!
# Descending the y-direction chart map

The compatible maps on the two ratio opens descend to the entire y-direction
equation chart. Both restriction identities and compatibility with the
original cubic contraction are retained by the descended morphism.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassModificationY

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The two actual local morphisms, indexed by the ratio cover. -/
def ratioChartMap (i : Fin 2) : (ratioCover W s b3 b4 b6).X i ⟶
    WeierstrassModificationX.modification W s b3 b4 b6 := by
  refine Fin.cases (scaleToModification W s b3 b4 b6) ?_ i
  intro j
  exact Fin.cases (horizontalToModification W s b3 b4 b6) (fun k => Fin.elim0 k) j

/-- The local morphisms agree on the categorical pullbacks used for descent. -/
theorem ratioChartMap_compatibility (i j : Fin 2) :
    pullback.fst ((ratioCover W s b3 b4 b6).f i) ((ratioCover W s b3 b4 b6).f j) ≫
        ratioChartMap W s b3 b4 b6 i =
      pullback.snd _ _ ≫ ratioChartMap W s b3 b4 b6 j := by
  fin_cases i <;> fin_cases j
  · congr 1
    exact (cancel_mono ((ratioCover W s b3 b4 b6).f (0 : Fin 2))).mp pullback.condition
  · change pullback.fst (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0))
      (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1)) ≫
        scaleToModification W s b3 b4 b6 =
      pullback.snd _ _ ≫ horizontalToModification W s b3 b4 b6
    rw [← cancel_epi (ratioIntersection_isPullback W s b3 b4 b6).isoPullback.hom]
    simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd]
    exact ratioIntersection_compatibility W s b3 b4 b6
  · change pullback.fst (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1))
      (PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0)) ≫
        horizontalToModification W s b3 b4 b6 =
      pullback.snd _ _ ≫ scaleToModification W s b3 b4 b6
    rw [← cancel_epi (ratioIntersection_isPullback W s b3 b4 b6).flip.isoPullback.hom]
    simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd]
    exact (ratioIntersection_compatibility W s b3 b4 b6).symm
  · congr 1
    exact (cancel_mono ((ratioCover W s b3 b4 b6).f (1 : Fin 2))).mp pullback.condition

/-- The actual morphism from the whole y-direction equation chart to the modification. -/
def yChart : Spec (.of (Coordinate W s b3 b4 b6)) ⟶
    WeierstrassModificationX.modification W s b3 b4 b6 :=
  (ratioCover W s b3 b4 b6).glueMorphisms (ratioChartMap W s b3 b4 b6)
    (ratioChartMap_compatibility W s b3 b4 b6)

/-- Descent recovers each of the two original local maps. -/
@[reassoc] theorem ratioCover_yChart (i : Fin 2) :
    (ratioCover W s b3 b4 b6).f i ≫ yChart W s b3 b4 b6 =
      ratioChartMap W s b3 b4 b6 i :=
  (ratioCover W s b3 b4 b6).ι_glueMorphisms _ _ i

/-- The scale-open restriction of the descended morphism. -/
@[reassoc] theorem scale_yChart :
    PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0) ≫ yChart W s b3 b4 b6 =
      scaleToModification W s b3 b4 b6 := ratioCover_yChart W s b3 b4 b6 0

/-- The horizontal-open restriction of the descended morphism. -/
@[reassoc] theorem horizontal_yChart :
    PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1) ≫ yChart W s b3 b4 b6 =
      horizontalToModification W s b3 b4 b6 := ratioCover_yChart W s b3 b4 b6 1

/-- The two prescribed local morphisms uniquely determine the whole-chart map. -/
theorem yChart_unique (g : Spec (.of (Coordinate W s b3 b4 b6)) ⟶
    WeierstrassModificationX.modification W s b3 b4 b6)
    (h0 : PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 0) ≫ g =
      scaleToModification W s b3 b4 b6)
    (h1 : PrincipalAffineRefinement.inclusion (coord W s b3 b4 b6 1) ≫ g =
      horizontalToModification W s b3 b4 b6) : g = yChart W s b3 b4 b6 := by
  apply (ratioCover W s b3 b4 b6).hom_ext
  intro i
  change Fin 2 at i
  rw [ratioCover_yChart]
  fin_cases i
  · exact h0
  · exact h1

/-- The descended chart retains the original cubic contraction globally. -/
@[reassoc] theorem yChart_contraction
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6) :
    yChart W s b3 b4 b6 ≫ WeierstrassModificationX.contraction W s b3 b4 b6 h3 h4 h6 =
      toCurve W s b3 b4 b6 h3 h4 h6 := by
  apply (ratioCover W s b3 b4 b6).hom_ext
  intro i
  change Fin 2 at i
  rw [ratioCover_yChart_assoc]
  fin_cases i
  · exact scaleToModification_contraction W s b3 b4 b6 h3 h4 h6
  · exact horizontalToModification_contraction W s b3 b4 b6 h3 h4 h6

end FLT.Mazur.WeierstrassModificationY
