/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.HomogeneousOne

/-!
# Explicit coordinates on homogeneous continuous two-cochains

The coordinates use consecutive differences, so evaluating at `(1,g,gh)`
recovers the inhomogeneous cochain. Local compactness justifies uncurrying.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

universe u

variable {k G M : Type u} [Field k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] [ContinuousSMul k M]

/-- Homogenize a jointly continuous two-cochain. -/
def homogeneousTwo (c : C(G × G, M)) : (coefficientComplex k G M).X 2 :=
  ⟨⟨fun g ↦ ⟨fun h ↦ ⟨fun j ↦ g • c (g⁻¹ * h, h⁻¹ * j), by fun_prop⟩, by
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : G × G ↦ g • c (g⁻¹ * z.1, z.1⁻¹ * z.2))
      fun_prop⟩, by
    apply ContinuousMap.continuous_of_continuous_uncurry
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (G × G) × G ↦ z.1.1 •
      c (z.1.1⁻¹ * z.1.2, z.1.2⁻¹ * z.2))
    fun_prop⟩, by
    intro g
    ext x y z
    change g • ((g⁻¹ * x) •
      c ((g⁻¹ * x)⁻¹ * (g⁻¹ * y), (g⁻¹ * y)⁻¹ * (g⁻¹ * z))) = _
    simp [smul_smul, mul_assoc]⟩

/-- Evaluate a homogeneous two-cochain on the vertices `(1,g,gh)`. -/
def inhomogeneousTwo (c : (coefficientComplex k G M).X 2) : C(G × G, M) :=
  (c.1 1).uncurry.comp ⟨fun z ↦ (z.1, z.1 * z.2), by fun_prop⟩

@[simp] theorem inhomogeneousTwo_homogeneousTwo (c : C(G × G, M)) :
    inhomogeneousTwo (homogeneousTwo (k := k) c) = c := by
  ext ⟨g, h⟩
  change (1 : G) • c (1⁻¹ * g, g⁻¹ * (g * h)) = c (g, h)
  simp

/-- Equivariance reconstructs a two-cochain from its inhomogeneous values. -/
theorem homogeneousTwo_inhomogeneousTwo (c : (coefficientComplex k G M).X 2) :
    homogeneousTwo (inhomogeneousTwo c) = c := by
  apply Subtype.ext
  ext g h j
  have hc := congrArg (fun f : C(G, C(G, C(G, M))) ↦ f g h j) (c.2 g)
  change g • c.1 (g⁻¹ * g) (g⁻¹ * h) (g⁻¹ * j) = c.1 g h j at hc
  simpa [homogeneousTwo, inhomogeneousTwo, mul_assoc] using hc

/-- The explicit continuous differential on one-cochains. -/
def continuousDifferentialOne (b : C(G, M)) : C(G × G, M) :=
  ⟨fun z ↦ z.1 • b z.2 - b (z.1 * z.2) + b z.1, by fun_prop⟩

omit [LocallyCompactSpace G] in
/-- Homogenization intertwines the degree-one differential. -/
theorem homogeneousTwo_differential (b : C(G, M)) :
    homogeneousTwo (k := k) (continuousDifferentialOne b) =
      (coefficientComplex k G M).d 1 2 (homogeneousOne b) := by
  apply Subtype.ext
  ext g h j
  rw [homogeneous_d_one]
  change g • ((g⁻¹ * h) • b (h⁻¹ * j) -
    b ((g⁻¹ * h) * (h⁻¹ * j)) + b (g⁻¹ * h)) = _
  simp [smul_add, smul_sub, smul_smul, mul_assoc]

omit [LocallyCompactSpace G] in
/-- The kernel of the homogeneous degree-two differential is the explicit cocycle equation. -/
theorem homogeneousTwo_cocycle_iff (c : C(G × G, M)) :
    (coefficientComplex k G M).d 2 3 (homogeneousTwo c) = 0 ↔
      groupCohomology.IsCocycle₂ c := by
  constructor
  · intro hc g h j
    have he := congrArg
      (fun f : (coefficientComplex k G M).X 3 ↦ f.1 1 g (g * h) (g * h * j)) hc
    change g • c (g⁻¹ * (g * h), (g * h)⁻¹ * (g * h * j)) -
      ((1 : G) • c (1⁻¹ * (g * h), (g * h)⁻¹ * (g * h * j)) -
      ((1 : G) • c (1⁻¹ * g, g⁻¹ * (g * h * j)) -
      (1 : G) • c (1⁻¹ * g, g⁻¹ * (g * h)))) = 0 at he
    simp only [mul_inv_rev, inv_mul_cancel_left, one_smul, inv_one, one_mul,
      mul_assoc] at he
    change c (g * h, j) + c (g, h) = g • c (h, j) + c (g, h * j)
    apply sub_eq_zero.mp
    calc
      c (g * h, j) + c (g, h) - (g • c (h, j) + c (g, h * j)) =
          -(g • c (h, j) - (c (g * h, j) - (c (g, h * j) - c (g, h)))) := by abel
      _ = 0 := by rw [he]; simp
  · intro hc
    apply Subtype.ext
    ext g h j l
    change h • c (h⁻¹ * j, j⁻¹ * l) -
      (g • c (g⁻¹ * j, j⁻¹ * l) -
      (g • c (g⁻¹ * h, h⁻¹ * l) - g • c (g⁻¹ * h, h⁻¹ * j))) = 0
    have he := congrArg (fun m : M ↦ g • m) (hc (g⁻¹ * h) (h⁻¹ * j) (j⁻¹ * l))
    simp only [smul_add, smul_smul, mul_assoc, mul_inv_cancel_left] at he
    calc
      _ = (h • c (h⁻¹ * j, j⁻¹ * l) + g • c (g⁻¹ * h, h⁻¹ * l)) -
          (g • c (g⁻¹ * j, j⁻¹ * l) + g • c (g⁻¹ * h, h⁻¹ * j)) := by abel
      _ = 0 := sub_eq_zero.mpr he.symm

end GaloisRepresentation.Extensions
