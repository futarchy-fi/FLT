/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialFamilyAmbient

/-!
# Naturality and chart comparison for polynomial ambient maps

The ambient lift commutes with scalar extension and agrees with the explicit
ambient map of a prescribed-basis parameter.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- Ambient lifts respect scalar extension of a parameter. -/
theorem polynomialAmbientMap_baseChange
    (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
    (hf : f ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (T : Type u) [CommRing T] [Algebra R T] (a : S →ₐ[R] T)
    (g : Spec (.of T) ⟶ polynomialHilbertScheme R I d)
    (hg : g ≫ polynomialHilbertStructure R I d =
      Spec.map (CommRingCat.ofHom (algebraMap R T)))
    (ha : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ f = g) :
    Spec.map (CommRingCat.ofHom (MvPolynomial.map a.toRingHom)) ≫
        polynomialAmbientMap R I d S f hf = polynomialAmbientMap R I d T g hg := by
  apply pullback.hom_ext
  · rw [Category.assoc, polynomialAmbientMap_fst, polynomialAmbientMap_fst, ← ha]
    simp only [← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact MvPolynomial.map_C a.toRingHom
  · rw [Category.assoc, polynomialAmbientMap_snd, polynomialAmbientMap_snd,
      ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    change (MvPolynomial.map a.toRingHom).comp
      (MvPolynomial.map (algebraMap R S)) = MvPolynomial.map (algebraMap R T)
    ext x <;> simp

/-- Cache the coefficient ring for ambient parameter comparison. -/
local instance naturalityCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache each chart ring for ambient parameter comparison. -/
local instance naturalityChartRing (w : Fin d → MvPolynomial I R) :
    CommRing (ChartRing R I d w) := inferInstance

/-- Ambient lifting of a chart parameter recovers its explicit polynomial chart map. -/
theorem polynomialAmbientMap_parameter (w : Fin d → MvPolynomial I R)
    (a : ChartRing R I d w →ₐ[R] S)
    (h : (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ polynomialHilbertChartι R I d w) ≫
      polynomialHilbertStructure R I d = Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    polynomialAmbientMap R I d S
        (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ polynomialHilbertChartι R I d w) h =
      polynomialParameterAmbientMap R I d w a := by
  apply pullback.hom_ext
  · rw [polynomialAmbientMap_fst, polynomialParameterAmbientMap_fst]
  · rw [polynomialAmbientMap_snd, polynomialParameterAmbientMap, Category.assoc,
      polynomialHilbertAmbientChart_snd, chartPolynomialOriginal, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    change MvPolynomial.map (algebraMap R S) = (MvPolynomial.map a.toRingHom).comp
      (MvPolynomial.map (algebraMap R (ChartRing R I d w)))
    ext x <;> simp

end FLT.Mazur.HilbertChart
