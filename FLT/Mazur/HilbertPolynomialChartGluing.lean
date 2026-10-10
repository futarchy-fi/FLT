/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartTransitionCocycle

/-!
# Gluing the polynomial Hilbert charts into an actual scheme

The constructed overlap isomorphisms and triple cocycle supply scheme gluing
data. The resulting scheme has the original chart spectra as an open cover.
Representability and the global universal ideal are separate constructions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)

/-- Actual gluing data for all prescribed polynomial tuples of length `d`. -/
def polynomialHilbertGlueData : Scheme.GlueData where
  J := Fin d → MvPolynomial I R
  U w := Spec (.of (ChartRing R I d w))
  V p := (chartTupleTransitionOpen R I d p.1 p.2).toScheme
  f w v := (chartTupleTransitionOpen R I d w v).ι
  f_id w := chartTupleTransitionOpen_self_isIso R I d w
  t w v := chartTupleReverseMorphism R I d w v
  t_id w := chartTupleReverseMorphism_self R I d w
  t' w v z := chartTupleTripleMap R I d w v z
  t_fac w v z := chartTupleTripleMap_snd R I d w v z
  cocycle w v z := chartTupleTripleMap_cocycle R I d w v z
  f_open _ _ := inferInstance

/-- The actual scheme obtained by gluing the polynomial Hilbert charts. -/
def polynomialHilbertScheme : Scheme.{u} := (polynomialHilbertGlueData R I d).glued

/-- Inclusion of an original affine chart in the glued polynomial Hilbert scheme. -/
def polynomialHilbertChartι (w : Fin d → MvPolynomial I R) :
    Spec (.of (ChartRing R I d w)) ⟶ polynomialHilbertScheme R I d :=
  (polynomialHilbertGlueData R I d).ι w

/-- Every original affine chart is an open subscheme of the glued scheme. -/
instance polynomialHilbertChartι_isOpenImmersion (w : Fin d → MvPolynomial I R) :
    IsOpenImmersion (polynomialHilbertChartι R I d w) :=
  inferInstanceAs (IsOpenImmersion ((polynomialHilbertGlueData R I d).ι w))

/-- The original chart spectra form an actual open cover of the glued scheme. -/
def polynomialHilbertSchemeCover : (polynomialHilbertScheme R I d).OpenCover :=
  (polynomialHilbertGlueData R I d).openCover

/-- The glued chart inclusions identify points by the actual change-of-tuple morphism. -/
theorem polynomialHilbertChartι_transition (w v : Fin d → MvPolynomial I R) :
    chartTupleTransition R I d w v ≫ polynomialHilbertChartι R I d v =
      (chartTupleTransitionOpen R I d w v).ι ≫ polynomialHilbertChartι R I d w := by
  have h := (polynomialHilbertGlueData R I d).toGlueData.glue_condition w v
  change chartTupleReverseMorphism R I d w v ≫ (chartTupleTransitionOpen R I d v w).ι ≫
    polynomialHilbertChartι R I d v = _ at h
  rw [← Category.assoc, chartTupleReverseMorphism_ι] at h
  exact h

end FLT.Mazur.HilbertChart
