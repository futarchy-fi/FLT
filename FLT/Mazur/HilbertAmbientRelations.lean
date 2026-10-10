/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartPointFamily

/-!
# Actual closed equations imposing ambient affine relations

For an arbitrary ideal in the original polynomial ring, take every coordinate
of every relation in the free chart algebra. Their span is an actual ideal
of the chart ring, with no finiteness assumption on the ambient relations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

universe u v

variable (R : Type u) [CommRing R] (I : Type v) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient ring before constructing closed ambient equations. -/
local instance ambientRelationsCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart ring before constructing closed ambient equations. -/
local instance ambientRelationsChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- A coordinate of an original ambient polynomial in the actual universal chart algebra. -/
def ambientRelationEquation (p : MvPolynomial I R) (k : Fin d) : ChartRing R I d w :=
  chartMap R I d w ((basis R I d).repr (evaluation R I d p) k)

/-- The closed equation ideal imposing every original ambient relation. -/
def ambientRelationsIdeal (K : Ideal (MvPolynomial I R)) : Ideal (ChartRing R I d w) :=
  Ideal.span (Set.range fun pk : K × Fin d ↦ ambientRelationEquation R I d w pk.1.val pk.2)

/-- The actual closed ambient-relation chart ring. -/
abbrev AmbientChartRing (K : Ideal (MvPolynomial I R)) :=
  ChartRing R I d w ⧸ ambientRelationsIdeal R I d w K

/-- Every required coordinate lies in the constructed equation ideal. -/
theorem ambientRelationEquation_mem (K : Ideal (MvPolynomial I R))
    (p : MvPolynomial I R) (hp : p ∈ K) (k : Fin d) :
    ambientRelationEquation R I d w p k ∈ ambientRelationsIdeal R I d w K :=
  Ideal.subset_span ⟨(⟨p, hp⟩, k), rfl⟩

/-- The actual quotient chart kills all coordinates of all original ambient relations. -/
theorem ambientRelationEquation_quotient_zero (K : Ideal (MvPolynomial I R))
    (p : MvPolynomial I R) (hp : p ∈ K) (k : Fin d) :
    Ideal.Quotient.mk (ambientRelationsIdeal R I d w K)
      (ambientRelationEquation R I d w p k) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (ambientRelationEquation_mem R I d w K p hp k)

variable {S : Type*} [CommRing S]

/-- A chart map kills the equation ideal exactly when it kills every relation coordinate. -/
theorem ambientRelationsIdeal_le_ker_iff (K : Ideal (MvPolynomial I R))
    (f : ChartRing R I d w →+* S) :
    ambientRelationsIdeal R I d w K ≤ RingHom.ker f ↔
      ∀ p ∈ K, ∀ k, f (ambientRelationEquation R I d w p k) = 0 := by
  rw [ambientRelationsIdeal, Ideal.span_le]
  constructor
  · intro h p hp k
    exact h ⟨(⟨p, hp⟩, k), rfl⟩
  · rintro h _ ⟨⟨p, k⟩, rfl⟩
    exact h p.val p.property k

variable [Algebra R S] (f : ChartRing R I d w →ₐ[R] S)

/-- Relation coordinates specialize to coordinates in the actual free point quotient. -/
theorem pointBasis_repr_ambientRelation (p : MvPolynomial I R) (k : Fin d) :
    (pointBasis R I d w f).repr (MvPolynomial.aeval (pointGenerator R I d w f) p) k =
      f (ambientRelationEquation R I d w p k) := by
  let _ := pointScalars R I d w f
  let _ := pointTower R I d w f
  change (fiberBasis R I d w S).repr
    (MvPolynomial.aeval (fiberGenerator R I d w S) p) k = _
  rw [fiberGenerator_evaluation, fiberBasis_repr_inclusion]
  rfl

end FLT.Mazur.HilbertChart
