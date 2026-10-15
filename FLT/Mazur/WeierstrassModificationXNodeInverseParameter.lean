/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactors
public import FLT.Mazur.NilpotentPolynomialInverseBaseChange

/-!
# Constructing the initial node's inverse incidence parameter

For q=v-r(t), the first node coordinate is p=t(q+a₁+2r(t)+b₃t).
On D(q+a₁), finite nilpotent iteration recovers t from p and q.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (b3 : R) (r : R[X])

/-- The nilpotent correction to the unit-linear incidence equation. -/
def nodeIncidenceCorrection : R[X] := X * (r + r + C b3 * X)

variable (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)

include hrI h3 in
/-- All coefficients of the nonlinear incidence correction lie in the arithmetic ideal. -/
theorem nodeIncidenceCorrection_mem : nodeIncidenceCorrection b3 r ∈ I.map C :=
  (I.map C).mul_mem_left _ ((I.map C).add_mem ((I.map C).add_mem hrI hrI)
    ((I.map C).mul_mem_right _ (Ideal.mem_map_of_mem C h3)))

variable (W : WeierstrassCurve R) {S : Type*} [CommRing S] [Algebra R S]
  (p q : S) (hu : IsUnit (q + algebraMap R S W.a₁))
local notation "f" => algebraMap R S

/-- The original incidence coordinate constructed from the two node coordinates. -/
def polynomialNodeInverseT : S :=
  NilpotentPolynomialInverse.extendedInverse I hI f (nodeIncidenceCorrection b3 r)
    (nodeIncidenceCorrection_mem b3 r I hrI h3) (q + f W.a₁) hu p

local notation "T" => polynomialNodeInverseT b3 r I hI hrI h3 W p q hu

/-- The inverse solves the original incidence-coordinate change exactly. -/
theorem polynomialNodeInverseT_equation :
    T * (q + f W.a₁ + (r.eval₂ f T + r.eval₂ f T + f b3 * T)) = p := by
  have h := NilpotentPolynomialInverse.extendedInverse_equation I hI f
    (nodeIncidenceCorrection b3 r) (nodeIncidenceCorrection_mem b3 r I hrI h3)
    (q + f W.a₁) hu p
  change (q + f W.a₁) * T + (nodeIncidenceCorrection b3 r).eval₂ f T = p at h
  simp only [nodeIncidenceCorrection, eval₂_mul, eval₂_add, eval₂_C, eval₂_X] at h
  linear_combination h

include hrI h3 hI hu in
/-- The original coordinate change has only one inverse incidence parameter. -/
theorem polynomialNodeParameter_unique {z w : S}
    (hz : z * (q + f W.a₁ + (r.eval₂ f z + r.eval₂ f z + f b3 * z)) = p)
    (hw : w * (q + f W.a₁ + (r.eval₂ f w + r.eval₂ f w + f b3 * w)) = p) : z = w := by
  apply NilpotentPolynomialInverse.extended_solution_unique I hI f
    (nodeIncidenceCorrection b3 r) (nodeIncidenceCorrection_mem b3 r I hrI h3)
    (q + f W.a₁) hu p
  · simp only [nodeIncidenceCorrection, eval₂_mul, eval₂_add, eval₂_C, eval₂_X]
    linear_combination hz
  · simp only [nodeIncidenceCorrection, eval₂_mul, eval₂_add, eval₂_C, eval₂_X]
    linear_combination hw

end FLT.Mazur.WeierstrassModificationX
