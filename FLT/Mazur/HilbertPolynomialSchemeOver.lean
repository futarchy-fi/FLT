/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialChartGluing

/-!
# The glued polynomial Hilbert scheme over its coefficient base

The actual structural maps of the affine charts descend because their
constructed transition morphisms respect the coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)

/-- The actual structure morphism of the glued polynomial Hilbert scheme. -/
def polynomialHilbertStructure : polynomialHilbertScheme R I d ⟶ Spec (.of R) :=
  Multicoequalizer.desc (polynomialHilbertGlueData R I d).toGlueData.diagram (Spec (.of R))
    (fun w ↦ Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w)))) (by
      rintro ⟨w, v⟩
      change (chartTupleTransitionOpen R I d w v).ι ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w))) =
        (chartTupleReverseMorphism R I d w v ≫ (chartTupleTransitionOpen R I d v w).ι) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d v)))
      rw [chartTupleReverseMorphism_ι]
      exact (chartTupleTransition_over R I d w v).symm)

/-- Each original affine chart lies over its original coefficient spectrum. -/
@[reassoc]
theorem polynomialHilbertChartι_over (w : Fin d → MvPolynomial I R) :
    polynomialHilbertChartι R I d w ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d w))) := by
  change Multicoequalizer.π (polynomialHilbertGlueData R I d).toGlueData.diagram w ≫ _ = _
  exact Multicoequalizer.π_desc (polynomialHilbertGlueData R I d).toGlueData.diagram
    (Spec (.of R)) _ _ w

end FLT.Mazur.HilbertChart
