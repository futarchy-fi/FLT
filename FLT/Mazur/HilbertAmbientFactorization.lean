/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAmbientRelations
public import FLT.Mazur.HilbertChartPointIdeal

/-!
# The exact ambient closed factorization criterion

The constructed relation ideal vanishes at a chart point precisely when its
full polynomial quotient ideal contains the scalar extension of the original
ambient ideal. Thus the closed equations impose the actual ambient scheme.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient ring for ambient quotient maps. -/
local instance ambientFactorCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart ring for ambient quotient maps. -/
local instance ambientFactorChartRing : CommRing (ChartRing R I d w) := inferInstance

variable {S : Type*} [CommRing S] [Algebra R S]
variable (f : ChartRing R I d w →ₐ[R] S)

/-- An original polynomial vanishes in the actual point quotient iff all its coordinates do. -/
theorem pointEvaluation_relation_zero_iff (p : MvPolynomial I R) :
    pointEvaluation R I d w f (MvPolynomial.map (algebraMap R S) p) = 0 ↔
      ∀ k, f (ambientRelationEquation R I d w p k) = 0 := by
  rw [pointEvaluation_map]
  constructor
  · intro h k
    rw [← pointBasis_repr_ambientRelation, h, map_zero]
    rfl
  · intro h
    apply (pointBasis R I d w f).repr.injective
    ext k
    rw [pointBasis_repr_ambientRelation, h, map_zero]
    rfl

/-- The closed chart equations are equivalent to containment of the entire ambient ideal. -/
theorem ambientRelationsIdeal_le_ker_point_iff (K : Ideal (MvPolynomial I R)) :
    ambientRelationsIdeal R I d w K ≤ RingHom.ker f.toRingHom ↔
      K.map (MvPolynomial.map (algebraMap R S)) ≤ pointIdeal R I d w f := by
  rw [ambientRelationsIdeal_le_ker_iff, Ideal.map_le_iff_le_comap]
  constructor
  · intro h p hp
    change pointEvaluation R I d w f (MvPolynomial.map (algebraMap R S) p) = 0
    exact (pointEvaluation_relation_zero_iff R I d w f p).mpr (h p hp)
  · intro h p hp
    exact (pointEvaluation_relation_zero_iff R I d w f p).mp (h hp)

/-- The actual chart point of a family contained in the ambient scheme factors through its ring. -/
def ambientChartLift (K : Ideal (MvPolynomial I R))
    (h : K.map (MvPolynomial.map (algebraMap R S)) ≤ pointIdeal R I d w f) :
    AmbientChartRing R I d w K →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ f ((ambientRelationsIdeal_le_ker_point_iff R I d w f K).mpr h)

/-- The constructed lift recovers the original polynomial Hilbert chart parameter. -/
theorem ambientChartLift_comp (K : Ideal (MvPolynomial I R))
    (h : K.map (MvPolynomial.map (algebraMap R S)) ≤ pointIdeal R I d w f) :
    (ambientChartLift R I d w f K h).comp
      (Ideal.Quotient.mkₐ R (ambientRelationsIdeal R I d w K)) = f :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- A lift through the actual ambient relation quotient is unique. -/
theorem ambientChartLift_unique (K : Ideal (MvPolynomial I R))
    (h : K.map (MvPolynomial.map (algebraMap R S)) ≤ pointIdeal R I d w f)
    (g : AmbientChartRing R I d w K →ₐ[R] S)
    (hg : g.comp (Ideal.Quotient.mkₐ R (ambientRelationsIdeal R I d w K)) = f) :
    g = ambientChartLift R I d w f K h := by
  apply Ideal.Quotient.algHom_ext
  exact hg.trans (ambientChartLift_comp R I d w f K h).symm

end FLT.Mazur.HilbertChart
