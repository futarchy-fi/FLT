/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeLabelHom

/-!
# Nodal labels are unchanged by multiplying the uniformizer by a unit

Changing π to πu rescales both divided coordinates by u⁻ᵏ. Their depth and
vanishing branch remain unchanged, so the actual point and component labels
are independent of this choice of uniformizer.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

/-- Multiplying a divided branch coordinate by a unit does not change its label. -/
theorem nodeBranchLabel_unit_mul {R : Type*} [CommRing R] [IsLocalRing R]
    (n k : ℕ) (b : R) {u : R} (hu : IsUnit u) :
    nodeBranchLabel n k (u * b) = nodeBranchLabel n k b := by
  classical
  simp only [nodeBranchLabel, (maximalIdeal R).unit_mul_mem_iff_mem hu]

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {P : (W.map (algebraMap A K)).toProjective.Point}

/-- Rescale a coordinate witness when the uniformizer is multiplied by a unit. -/
noncomputable def NodePointCoordinates.changeUniformizer (v : NodePointCoordinates A W π P)
    (u : Aˣ) : NodePointCoordinates A W (π * u) P := by
  let a := (↑u⁻¹ : A) ^ v.depth * v.a
  let b := (↑u⁻¹ : A) ^ v.depth * v.b
  have hx : (π * ↑u) ^ v.depth * a = π ^ v.depth * v.a := by
    dsimp [a]
    rw [mul_pow, mul_assoc, ← mul_assoc ((↑u : A) ^ v.depth), ← mul_pow]
    simp
  have hy : (π * ↑u) ^ v.depth * b = π ^ v.depth * v.b := by
    dsimp [b]
    rw [mul_pow, mul_assoc, ← mul_assoc ((↑u : A) ^ v.depth), ← mul_pow]
    simp
  have hs : (W.map (algebraMap A K)).toAffine.Nonsingular
      (((π * ↑u) ^ v.depth * a : A) : K) (((π * ↑u) ^ v.depth * b : A) : K) := by
    rw [hx, hy]
    exact v.nonsingular
  refine ⟨v.depth, a, b, ?_, hs, ?_⟩
  · exact v.primitive.imp ((u⁻¹.isUnit.pow v.depth).mul) ((u⁻¹.isUnit.pow v.depth).mul)
  · apply v.represents.trans
    apply congrArg Affine.Point.toProjective
    simp only [Affine.Point.some.injEq]
    exact ⟨congrArg Subtype.val hx.symm, congrArg Subtype.val hy.symm⟩

/-- The actual point label is invariant under a unit change of uniformizer. -/
theorem nodePointLabel_mul_uniformizer {n : ℕ} (D : SplitNodeDepth W π n) (u : Aˣ)
    (D' : SplitNodeDepth W (π * ↑u) n)
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D' P = nodePointLabel D P := by
  by_cases hP : SmoothReduction A W P
  · rw [(nodePointLabel_eq_zero_iff D' P).mpr hP, (nodePointLabel_eq_zero_iff D P).mpr hP]
  · obtain ⟨v, _⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
      D.a₃_mem D.a₄_mem D.a₆_not_mem P hP
    rw [nodePointLabel_eq_of_coordinates D v,
      nodePointLabel_eq_of_coordinates D' (v.changeUniformizer u)]
    exact nodeBranchLabel_unit_mul n v.depth v.b (u⁻¹.isUnit.pow v.depth)

/-- The canonical component label is invariant under a unit change of uniformizer. -/
theorem nodeComponentLabel_mul_uniformizer {n : ℕ} (D : SplitNodeDepth W π n) (u : Aˣ)
    (D' : SplitNodeDepth W (π * ↑u) n) (c : EllipticComponentQuotient A W) :
    nodeComponentLabel D' c = nodeComponentLabel D c := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  exact nodePointLabel_mul_uniformizer D u D' P

/-- Two generators of the maximal ideal give the same actual point label. -/
theorem nodePointLabel_uniformizer_independent {π' : A} {n : ℕ}
    (D : SplitNodeDepth W π n) (D' : SplitNodeDepth W π' n)
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D' P = nodePointLabel D P := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp
    (D.maximalIdeal_eq.symm.trans D'.maximalIdeal_eq)
  subst π'
  exact nodePointLabel_mul_uniformizer D u D' P

/-- The canonical component label is independent of the generator of the maximal ideal. -/
theorem nodeComponentLabel_uniformizer_independent {π' : A} {n : ℕ}
    (D : SplitNodeDepth W π n) (D' : SplitNodeDepth W π' n)
    (c : EllipticComponentQuotient A W) : nodeComponentLabel D' c = nodeComponentLabel D c := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  exact nodePointLabel_uniformizer_independent D D' P

end FLT.Mazur
