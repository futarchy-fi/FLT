/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialAmbientOverlap

/-!
# Comparing the actual universal closed families on common ambient tests

The equality of ideal sheaves gives an isomorphism of actual pullback closed
subschemes over every common test. These comparisons preserve the closed
immersions and satisfy identity and composition laws.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)

/-- Cache the coefficients for ambient closed-family inference. -/
local instance closedComparisonCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache each chart ring for ambient closed-family inference. -/
local instance closedComparisonChartRing (w : Fin d → MvPolynomial I R) :
    CommRing (ChartRing R I d w) := inferInstance
variable (w v z : Fin d → MvPolynomial I R)
variable {X : Scheme.{u}}

/-- The actual pullback closed families on any common ambient test are isomorphic. -/
def chartClosedFamilyComparison
    (f : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d w))))
    (g : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d v))))
    (h : f ≫ polynomialHilbertAmbientChart R I d w =
      g ≫ polynomialHilbertAmbientChart R I d v) :
    pullback f (chartPolynomialIdealSheaf R I d w).subschemeι ≅
      pullback g (chartPolynomialIdealSheaf R I d v).subschemeι :=
  ((chartPolynomialIdealSheaf R I d w).comapIso f).symm ≪≫
    subschemeCongr (chartPolynomialIdealSheaf_commonAmbient R I d w v f g h) ≪≫
      (chartPolynomialIdealSheaf R I d v).comapIso g

/-- The closed-family comparison respects the actual immersion into the test scheme. -/
@[reassoc]
theorem chartClosedFamilyComparison_fst
    (f : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d w))))
    (g : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d v))))
    (h : f ≫ polynomialHilbertAmbientChart R I d w =
      g ≫ polynomialHilbertAmbientChart R I d v) :
    (chartClosedFamilyComparison R I d w v f g h).hom ≫ pullback.fst _ _ =
      pullback.fst f (chartPolynomialIdealSheaf R I d w).subschemeι := by
  simp [chartClosedFamilyComparison]

/-- The comparison on an identical ambient test is the identity morphism. -/
theorem chartClosedFamilyComparison_self
    (f : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d w)))) :
    (chartClosedFamilyComparison R I d w w f f rfl).hom = 𝟙 _ := by
  rw [← cancel_mono (pullback.fst f (chartPolynomialIdealSheaf R I d w).subschemeι),
    chartClosedFamilyComparison_fst, Category.id_comp]

/-- Successive actual closed-family comparisons satisfy the composition law. -/
theorem chartClosedFamilyComparison_comp
    (f : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d w))))
    (g : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d v))))
    (k : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d z))))
    (hfg : f ≫ polynomialHilbertAmbientChart R I d w =
      g ≫ polynomialHilbertAmbientChart R I d v)
    (hgk : g ≫ polynomialHilbertAmbientChart R I d v =
      k ≫ polynomialHilbertAmbientChart R I d z) :
    (chartClosedFamilyComparison R I d w v f g hfg).hom ≫
        (chartClosedFamilyComparison R I d v z g k hgk).hom =
      (chartClosedFamilyComparison R I d w z f k (hfg.trans hgk)).hom := by
  rw [← cancel_mono (pullback.fst k (chartPolynomialIdealSheaf R I d z).subschemeι),
    Category.assoc, chartClosedFamilyComparison_fst, chartClosedFamilyComparison_fst,
    chartClosedFamilyComparison_fst]

/-- The actual closed families are identified on the full intersection of ambient charts. -/
def chartClosedFamilyOverlapIso :
    pullback (pullback.fst (polynomialHilbertAmbientChart R I d w)
      (polynomialHilbertAmbientChart R I d v))
      (chartPolynomialIdealSheaf R I d w).subschemeι ≅
    pullback (pullback.snd (polynomialHilbertAmbientChart R I d w)
      (polynomialHilbertAmbientChart R I d v))
      (chartPolynomialIdealSheaf R I d v).subschemeι :=
  chartClosedFamilyComparison R I d w v _ _ pullback.condition

end FLT.Mazur.HilbertChart
