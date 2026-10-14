/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodePointParameter

/-!
# Nonvanishing of the original component parameter

Every nonsmooth original point has a nonzero normalized parameter. Together
with the original smooth character, this packages every generic point into
residue-field units without choosing a root of the period coefficient.
-/

@[expose] public noncomputable section
namespace FLT.Mazur
open IsLocalRing
variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n) (c₆ : A)
  {P : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- A positive strict branch has a unit positive tangent. -/
theorem node_positive_tangent_isUnit (v : NodePointCoordinates A W π P)
    (hv0 : 0 < v.depth) (hv : 2 * v.depth < n) (hb : v.b ∈ maximalIdeal A) :
    IsUnit (v.b + W.a₁ * v.a) := by
  rcases (node_point_branches_below_middle W D.uniformizer_ne_zero D.maximalIdeal_eq
    n v.depth hv0 hv D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
    v.a v.b v.primitive v.equation).2 with h | h
  · exact h.2
  · exact (hb h.1).elim

/-- Every bounded positive-depth primitive parameter is nonzero. -/
theorem nodeCoordinateParameter_ne_zero (h6 : W.a₆ = π ^ n * c₆)
    (v : NodePointCoordinates A W π P) (hv0 : 0 < v.depth) (hv : v.depth ≤ n / 2) :
    nodeCoordinateParameter n c₆ v ≠ 0 := by
  classical
  by_cases hm : 2 * v.depth = n
  · simp only [nodeCoordinateParameter, hm, true_or, ite_true]
    exact nodePositiveParameter_ne_zero D v (v.units_of_middle D hm).2
  by_cases hb : v.b ∈ maximalIdeal A
  · simp only [nodeCoordinateParameter, hb, or_true, ite_true]
    exact nodePositiveParameter_ne_zero D v (node_positive_tangent_isUnit D v hv0 (by omega) hb)
  · simp only [nodeCoordinateParameter, hm, hb, or_self, ite_false]
    exact mul_ne_zero (nodeWrapParameter_ne_zero D c₆ h6)
      (nodeNegativeParameter_ne_zero D v (not_not.mp hb))

/-- The global original parameter never vanishes. -/
theorem nodePointParameter_ne_zero (h6 : W.a₆ = π ^ n * c₆)
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointParameter D c₆ P ≠ 0 := by
  classical
  by_cases hp : SmoothReduction A W P
  · rw [nodePointParameter_smooth D c₆ ⟨P, hp⟩]
    exact Units.ne_zero _
  obtain ⟨v, hv⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
    D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
  rw [nodePointParameter_of_coordinates D c₆ v hp]
  exact nodeCoordinateParameter_ne_zero D c₆ h6 v (v.depth_pos_of_not_smooth D hp) hv

/-- The original global parameter, now valued in residue-field units. -/
def nodePointParameterUnit (h6 : W.a₆ = π ^ n * c₆)
    (P : (W.map (algebraMap A K)).toProjective.Point) : (ResidueField A)ˣ :=
  Units.mk0 _ (nodePointParameter_ne_zero D c₆ h6 P)

/-- Forgetting the unit recovers exactly the original parameter. -/
@[simp] theorem nodePointParameterUnit_val (h6 : W.a₆ = π ^ n * c₆)
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    (nodePointParameterUnit D c₆ h6 P).val = nodePointParameter D c₆ P := rfl

/-- The period coefficient also defines a residue-field unit. -/
def nodeWrapParameterUnit (h6 : W.a₆ = π ^ n * c₆) : (ResidueField A)ˣ :=
  Units.mk0 _ (nodeWrapParameter_ne_zero D c₆ h6)

/-- Forgetting the period unit retains the actual original coefficient. -/
@[simp] theorem nodeWrapParameterUnit_val (h6 : W.a₆ = π ^ n * c₆) :
    (nodeWrapParameterUnit D c₆ h6).val = nodeWrapParameter W c₆ := rfl

end FLT.Mazur
