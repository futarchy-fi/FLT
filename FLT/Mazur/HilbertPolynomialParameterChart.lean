/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialParameterIdeal

/-!
# Coordinate ideals on Hilbert chart tests

On any affine test factoring through a prescribed-basis chart, the parameter
ideal becomes the chart point's full ideal, including nonreduced structure.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (S : Type u) [CommRing S] [Algebra R S]

/-- Cache coefficient rings while comparing chart ideals. -/
local instance parameterChartCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache chart rings while comparing chart ideals. -/
local instance parameterChartRing (w : Fin d → MvPolynomial I R) :
    CommRing (ChartRing R I d w) := inferInstance

attribute [local irreducible] pointIdeal

/-- A chart-valued parameter has exactly its prescribed-basis point ideal. -/
theorem polynomialParameterIdeal_chart (w : Fin d → MvPolynomial I R)
    (a : ChartRing R I d w →ₐ[R] S)
    (ha : (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ polynomialHilbertChartι R I d w) ≫
      polynomialHilbertStructure R I d = Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    polynomialParameterIdeal R I d S
      (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ polynomialHilbertChartι R I d w) ha =
      pointIdeal R I d w a := by
  unfold polynomialParameterIdeal
  rw [polynomialAmbientMap_parameter R I d S w a ha]
  rw [polynomialUniversalIdeal_parameterPullback R I d w a, coordinateIdeal_baseIdeal]

variable (f : Spec (.of S) ⟶ polynomialHilbertScheme R I d)
variable (hf : f ≫ polynomialHilbertStructure R I d =
  Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- Any affine factorization through a Hilbert chart identifies the extended parameter ideal. -/
theorem polynomialParameterIdeal_affineChart
    (T : Type u) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (w : Fin d → MvPolynomial I R) (a : ChartRing R I d w →ₐ[R] T)
    (ha : Spec.map (CommRingCat.ofHom (algebraMap S T)) ≫ f =
      Spec.map (CommRingCat.ofHom a.toRingHom) ≫ polynomialHilbertChartι R I d w) :
    (polynomialParameterIdeal R I d S f hf).map (MvPolynomial.map (algebraMap S T)) =
      pointIdeal R I d w a := by
  have hg : (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ polynomialHilbertChartι R I d w) ≫
      polynomialHilbertStructure R I d = Spec.map (CommRingCat.ofHom (algebraMap R T)) := by
    rw [← ha, Category.assoc, hf, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq R S T).symm
  exact (polynomialParameterIdeal_baseChange R I d S f hf T
    (IsScalarTower.toAlgHom R S T) _ hg ha).symm.trans
      (polynomialParameterIdeal_chart R I d T w a hg)

end FLT.Mazur.HilbertChart
