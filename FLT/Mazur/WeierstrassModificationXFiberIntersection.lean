/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberConicGeometry

/-!
# The actual incidence-conic intersection

The sum of the two original component ideals has coordinate algebra
R[v]/(v*(v+a)). This retains scheme structure and both oriented intersection
points; the middle-depth coefficient disappears only after setting t=0.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassModificationX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (a c : R)

/-- The actual scheme-theoretic intersection ideal in the full horizontal fiber. -/
def fiberIntersectionIdeal : Ideal (FiberCoordinate a c) :=
  Ideal.span {fiberT a c} ⊔ fiberConicIdeal a c

/-- The oriented intersection algebra on the incidence line. -/
abbrev IntersectionCoordinate := R[X] ⧸ Ideal.span {X * (X + C a)}

/-- The full fiber intersection is exactly the two-root incidence-line equation. -/
def fiberIntersectionEquiv :
    (FiberCoordinate a c ⧸ fiberIntersectionIdeal a c) ≃ₐ[R] IntersectionCoordinate a :=
  (DoubleQuot.quotQuotEquivQuotSupₐ R
    (Ideal.span {fiberT a c}) (fiberConicIdeal a c)).symm.trans
      (Ideal.quotientEquivAlg _ _ (incidenceQuotientEquiv a c) (by
        simp only [fiberConicIdeal, Ideal.map_span, Set.image_singleton,
          Ideal.Quotient.mkₐ_eq_mk]
        congr 1
        congr 1
        exact (incidenceQuotientEquiv_mk a c (fiberConicFactor a c)).trans
          (fiberIncidenceMap_factor a c) |>.symm))

/-- The incidence and conic meet only at the two original tangent slopes, at every prime. -/
theorem fiber_intersection_prime_slopes (p : PrimeSpectrum (FiberCoordinate a c))
    (ht : fiberT a c ∈ p.asIdeal) (hc : fiberConicFactor a c ∈ p.asIdeal) :
    fiberV a c ∈ p.asIdeal ∨ fiberV a c + algebraMap R _ a ∈ p.asIdeal := by
  apply p.isPrime.mem_or_mem
  have hterm : algebraMap R (FiberCoordinate a c) c * fiberT a c ^ 2 ∈ p.asIdeal := by
    rw [pow_two]
    exact p.asIdeal.mul_mem_left _ (p.asIdeal.mul_mem_left _ ht)
  have h := p.asIdeal.add_mem hc hterm
  simpa only [fiberConicFactor, sub_add_cancel] using h

/-- The two intersection slopes cannot meet when the original tangent difference is a unit. -/
theorem fiber_intersection_slopes_disjoint (ha : IsUnit a)
    (p : PrimeSpectrum (FiberCoordinate a c)) :
    ¬ (fiberV a c ∈ p.asIdeal ∧ fiberV a c + algebraMap R _ a ∈ p.asIdeal) := by
  rintro ⟨h0, h1⟩
  have hu : algebraMap R (FiberCoordinate a c) a ∈ p.asIdeal := by
    simpa only [add_sub_cancel_left] using p.asIdeal.sub_mem h1 h0
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hu (ha.map (algebraMap R _)))

end FLT.Mazur.WeierstrassModificationX
