/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.ContinuousCup
public import FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Explicit coordinates on homogeneous continuous cochains in degrees zero and one

The action is jointly continuous. Local compactness is needed later to uncurry
homogeneous cochains; all coordinate maps here preserve the actual topology.
-/

@[expose] public section

namespace GaloisRepresentation.Extensions

universe u

variable (k G M : Type u) [Field k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
    [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M] [ContinuousSMul k M]

/-- The topological representation attached to the given discrete coefficient action. -/
def coefficientRepresentation : ContRepresentation k G M where
  toMonoidHom.toFun g :=
    { toFun := fun m ↦ g • m
      map_add' := smul_add g
      map_smul' := fun r m ↦ smul_comm g r m
      cont := continuous_const_smul g }
  toMonoidHom.map_one' := by ext m; exact one_smul G m
  toMonoidHom.map_mul' g h := by ext m; exact mul_smul g h m

/-- The actual homogeneous continuous cochain complex for these coefficients. -/
abbrev coefficientComplex := TopRep.homogeneousCochains
  (TopRep.of (coefficientRepresentation k G M))

variable {k G M}

/-- A coefficient as an equivariant homogeneous zero-cochain. -/
def homogeneousZero (a : M) : (coefficientComplex k G M).X 0 :=
  ⟨⟨fun g ↦ g • a, continuous_id.smul continuous_const⟩, by
    intro g
    ext x
    change g • ((g⁻¹ * x) • a) = x • a
    simp [smul_smul]⟩

/-- Equivariance reconstructs a zero-cochain from its value at one. -/
theorem homogeneousZero_eval (c : (coefficientComplex k G M).X 0) :
    homogeneousZero (c.1 1) = c := by
  apply Subtype.ext
  ext g
  have hc := congrArg (fun f : C(G, M) ↦ f g) (c.2 g)
  change g • c.1 (g⁻¹ * g) = c.1 g at hc
  simpa [homogeneousZero] using hc

/-- Homogenize a continuous one-cochain. -/
def homogeneousOne (c : C(G, M)) : (coefficientComplex k G M).X 1 :=
  ⟨(⟨fun z : G × G ↦ z.1 • c (z.1⁻¹ * z.2),
    continuous_fst.smul (c.continuous.comp (continuous_fst.inv.mul continuous_snd))⟩ :
      C(G × G, M)).curry, by
    intro g
    ext x y
    change g • ((g⁻¹ * x) • c ((g⁻¹ * x)⁻¹ * (g⁻¹ * y))) =
      x • c (x⁻¹ * y)
    simp [smul_smul, mul_assoc]⟩

/-- Evaluate a homogeneous one-cochain at its first vertex equal to one. -/
def inhomogeneousOne (c : (coefficientComplex k G M).X 1) : C(G, M) := c.1 1

@[simp] theorem inhomogeneousOne_homogeneousOne (c : C(G, M)) :
    inhomogeneousOne (homogeneousOne (k := k) c) = c := by
  ext g
  change (1 : G) • c (1⁻¹ * g) = c g
  simp

/-- Equivariance reconstructs a one-cochain from its values at `(1,g)`. -/
theorem homogeneousOne_inhomogeneousOne (c : (coefficientComplex k G M).X 1) :
    homogeneousOne (inhomogeneousOne c) = c := by
  apply Subtype.ext
  ext g h
  have hc := congrArg (fun f : C(G, C(G, M)) ↦ f g h) (c.2 g)
  change g • c.1 (g⁻¹ * g) (g⁻¹ * h) = c.1 g h at hc
  simpa [homogeneousOne, inhomogeneousOne] using hc

/-- The homogeneous zero differential is the usual principal cocycle. -/
theorem homogeneous_d_zero (a : M) (g h : G) :
    ((coefficientComplex k G M).d 0 1 (homogeneousZero a)).1 g h = h • a - g • a := by
  rfl

/-- The homogeneous one differential in explicit coordinates. -/
theorem homogeneous_d_one (c : C(G, M)) (g h j : G) :
    ((coefficientComplex k G M).d 1 2 (homogeneousOne c)).1 g h j =
      h • c (h⁻¹ * j) - g • c (g⁻¹ * j) + g • c (g⁻¹ * h) := by
  change h • c (h⁻¹ * j) - (g • c (g⁻¹ * j) - g • c (g⁻¹ * h)) = _
  abel

end GaloisRepresentation.Extensions
