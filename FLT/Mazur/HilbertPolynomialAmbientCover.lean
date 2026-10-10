/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialAmbient

/-!
# Covering the global ambient space by actual polynomial spectra

The polynomial-spectrum charts are the inverse images of the parameter
charts. Their pullback comparisons transport the pulled-back parameter cover
to an open cover whose objects have the original coordinate rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)

/-- Cache the coefficients for ambient closed-family inference. -/
local instance ambientCoverCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache each chart ring for ambient closed-family inference. -/
local instance ambientCoverChartRing (w : Fin d → MvPolynomial I R) :
    CommRing (ChartRing R I d w) := inferInstance

/-- The actual polynomial spectra over the Hilbert charts cover the global ambient space. -/
def polynomialHilbertAmbientCover : (polynomialHilbertAmbient R I d).OpenCover where
  I₀ := Fin d → MvPolynomial I R
  X w := Spec (.of (MvPolynomial I (ChartRing R I d w)))
  f w := polynomialHilbertAmbientChart R I d w
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun w ↦ inferInstance⟩
    let C := (polynomialHilbertSchemeCover R I d).pullback₁
      (pullback.fst (polynomialHilbertStructure R I d)
        (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R)))))
    obtain ⟨w, y, hy⟩ := Scheme.Cover.exists_eq C x
    let q := polynomialHilbertAmbientChart_isPullback R I d w
    refine ⟨w, q.isoPullback.inv y, ?_⟩
    have he := congrArg (fun f ↦ f y) q.isoPullback_inv_fst
    exact he.trans hy

end FLT.Mazur.HilbertChart
