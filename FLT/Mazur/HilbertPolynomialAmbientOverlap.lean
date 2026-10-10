/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialAmbient

/-!
# Universal ideals on actual ambient overlaps

The transition domain is the categorical intersection of parameter charts.
Consequently two maps into ambient charts with the same global ambient map
pull back equal actual ideal sheaves. This includes the full ambient pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)

/-- Cache the coefficients for ambient closed-family inference. -/
local instance ambientOverlapCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache each chart ring for ambient closed-family inference. -/
local instance ambientOverlapChartRing (w : Fin d → MvPolynomial I R) :
    CommRing (ChartRing R I d w) := inferInstance
variable (w v : Fin d → MvPolynomial I R)

/-- The full transition domain is the actual intersection of the glued parameter charts. -/
theorem chartTupleTransition_isPullback :
    IsPullback (chartTupleTransitionOpen R I d w v).ι (chartTupleTransition R I d w v)
      (polynomialHilbertChartι R I d w) (polynomialHilbertChartι R I d v) := by
  have h := IsPullback.of_isLimit
    ((polynomialHilbertGlueData R I d).vPullbackConeIsLimit w v)
  change IsPullback (chartTupleTransitionOpen R I d w v).ι
    (chartTupleReverseMorphism R I d w v ≫ (chartTupleTransitionOpen R I d v w).ι)
    (polynomialHilbertChartι R I d w) (polynomialHilbertChartι R I d v) at h
  simpa only [chartTupleReverseMorphism_ι] using h

/-- Every common ambient test pulls back the same universal ideal sheaf. -/
theorem chartPolynomialIdealSheaf_commonAmbient {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d w))))
    (g : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d v))))
    (h : f ≫ polynomialHilbertAmbientChart R I d w =
      g ≫ polynomialHilbertAmbientChart R I d v) :
    (chartPolynomialIdealSheaf R I d w).comap f =
      (chartPolynomialIdealSheaf R I d v).comap g := by
  have hf := congrArg (· ≫ pullback.fst (polynomialHilbertStructure R I d)
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R))))) h
  simp only [Category.assoc, polynomialHilbertAmbientChart_fst] at hf
  have hp := congrArg (· ≫ pullback.snd (polynomialHilbertStructure R I d)
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R))))) h
  simp only [Category.assoc, polynomialHilbertAmbientChart_snd] at hp
  let q := chartTupleTransition_isPullback R I d w v
  let k := q.lift (f ≫ chartPolynomialProjection R I d w)
    (g ≫ chartPolynomialProjection R I d v) (by simpa only [Category.assoc] using hf)
  exact chartPolynomialIdealSheaf_transition R I d w v f g k
    (q.lift_fst _ _ _) (q.lift_snd _ _ _) hp

/-- The actual universal chart ideal sheaves agree on the full ambient fiber product. -/
theorem chartPolynomialIdealSheaf_pullbackOverlap :
    (chartPolynomialIdealSheaf R I d w).comap
        (pullback.fst (polynomialHilbertAmbientChart R I d w)
          (polynomialHilbertAmbientChart R I d v)) =
      (chartPolynomialIdealSheaf R I d v).comap
        (pullback.snd (polynomialHilbertAmbientChart R I d w)
          (polynomialHilbertAmbientChart R I d v)) :=
  chartPolynomialIdealSheaf_commonAmbient R I d w v _ _ pullback.condition

end FLT.Mazur.HilbertChart
