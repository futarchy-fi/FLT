/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineMorphismAlgebraMap
public import FLT.Mazur.HilbertPolynomialSchemeOver
public import FLT.Mazur.PolynomialRelativeCoverExtension

/-!
# Actual affine chart factorizations of every scheme parameter

Pull back the polynomial Hilbert chart cover and refine by affine opens.
Every resulting chart has a constructed algebra map to its prescribed-basis
parameter chart. These local factorizations require no choices in the input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
variable (f : X ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d = s)

/-- The actual affine refinement of the parameter's inverse image Hilbert chart cover. -/
def ambientParameterAffineCover : X.AffineOpenCover :=
  Scheme.OpenCover.affineRefinement ((polynomialHilbertSchemeCover R I d).pullback₁ f)

variable (i : (ambientParameterAffineCover R I d f).I₀)

/-- Each affine refinement chart maps to its original Hilbert parameter chart. -/
def ambientParameterCoverChart : Spec ((ambientParameterAffineCover R I d f).X i) ⟶
    Spec (.of (ChartRing R I d i.1)) :=
  (pullback f (polynomialHilbertChartι R I d i.1)).affineCover.f i.2 ≫
    pullback.snd f (polynomialHilbertChartι R I d i.1)

/-- The constructed chart factorization recovers the actual global parameter on that cover. -/
theorem ambientParameterCoverChart_factor :
    (ambientParameterAffineCover R I d f).f i ≫ f =
      ambientParameterCoverChart R I d f i ≫ polynomialHilbertChartι R I d i.1 := by
  change (_ ≫ pullback.fst f (polynomialHilbertChartι R I d i.1)) ≫ f = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  rfl

include hf

/-- The chart factorization respects the coefficient algebra of the affine base chart. -/
theorem ambientParameterCoverChart_over :
    let _ := polynomialAffineCoverAlgebra R s (ambientParameterAffineCover R I d f) i
    ambientParameterCoverChart R I d f i ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R I d i.1))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R ((ambientParameterAffineCover R I d f).X i))) := by
  let _ := polynomialAffineCoverAlgebra R s (ambientParameterAffineCover R I d f) i
  rw [← polynomialHilbertChartι_over, ← Category.assoc,
    ← ambientParameterCoverChart_factor, Category.assoc, hf]
  exact polynomialAffineCoverAlgebra_over R s (ambientParameterAffineCover R I d f) i

/-- The actual algebra map of the prescribed-basis parameter on each affine covering chart. -/
def ambientParameterCoverAlgHom :
    let _ := polynomialAffineCoverAlgebra R s (ambientParameterAffineCover R I d f) i
    ChartRing R I d i.1 →ₐ[R] (ambientParameterAffineCover R I d f).X i := by
  let _ := polynomialAffineCoverAlgebra R s (ambientParameterAffineCover R I d f) i
  exact affineOverAlgHom R (ChartRing R I d i.1) ((ambientParameterAffineCover R I d f).X i)
    (ambientParameterCoverChart R I d f i)
    (ambientParameterCoverChart_over R I d s f hf i)

/-- Taking the spectrum of the constructed algebra map recovers the original affine chart map. -/
theorem ambientParameterCoverAlgHom_spec :
    let _ := polynomialAffineCoverAlgebra R s (ambientParameterAffineCover R I d f) i
    Spec.map (CommRingCat.ofHom (ambientParameterCoverAlgHom R I d s f hf i).toRingHom) =
      ambientParameterCoverChart R I d f i := by
  let _ := polynomialAffineCoverAlgebra R s (ambientParameterAffineCover R I d f) i
  exact affineOverAlgHom_spec R (ChartRing R I d i.1)
    ((ambientParameterAffineCover R I d f).X i) _
    (ambientParameterCoverChart_over R I d s f hf i)

end FLT.Mazur.HilbertChart
