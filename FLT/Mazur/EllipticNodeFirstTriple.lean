/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeFirstBranchSlope
public import FLT.Mazur.EllipticNodeThirdIntersection
public import FLT.Mazur.EllipticNodeTripleDepth

/-!
# Three first-branch points have depth sum n

For two first-branch summands whose negative sum is again on that branch,
the actual line-intersection identities force the three depths to sum to
the exact a₆ depth. This is the wraparound case of component-label addition.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- Three first-branch points on the actual addition line have depth sum n. -/
theorem node_depth_sum_of_first_triple
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (-(P + Q)))
    (hk : 0 < v.depth) (hkw : v.depth ≤ w.depth) (hw : 2 * w.depth < n)
    (hu : 0 < u.depth) (hun : 2 * u.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) (hf : u.b ∈ maximalIdeal A) :
    v.depth + w.depth + u.depth = n := by
  classical
  obtain ⟨l, hlm, hl, hxy⟩ := exists_node_first_branch_slope D v w hk hkw hw hb hd
  obtain ⟨hx3, hν3⟩ := node_third_intersection_coordinates v w u l hxy hl
  obtain ⟨hlineK, hsecondK⟩ := slope_cleared_identities _ v.nonsingular.1 w.nonsingular.1 hxy
  rw [hl] at hlineK hsecondK
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, ValuationSubring.algebraMap_apply] at hsecondK
  let x := π ^ v.depth * v.a
  let y := π ^ v.depth * v.b
  let z := π ^ w.depth * w.a
  let t := π ^ w.depth * w.b
  let ν := y - l * x
  have hline : (x - z) * l = y - t := by exact_mod_cast hlineK
  have hsecond : (y + t + W.a₁ * z + W.a₃) * l =
      x ^ 2 + x * z + z ^ 2 + W.a₂ * (x + z) + W.a₄ - W.a₁ * y := by
    exact_mod_cast hsecondK
  have hpair := node_line_pair_products W x y z t l hline hsecond
  have hprod := node_line_triple_product W x y z t l w.equation hline hsecond
  rw [← hx3] at hpair hprod
  have hπ : π ∈ maximalIdeal A := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hmem (k : ℕ) (a : A) : π ^ k * a ∈ maximalIdeal A ^ k :=
    (maximalIdeal A ^ k).mul_mem_right _ (Ideal.pow_mem_pow hπ k)
  have hint (k : ℕ) (a b : A) (hb : b ∈ maximalIdeal A) :
      π ^ k * b - l * (π ^ k * a) ∈ maximalIdeal A ^ (k + 1) := by
    have he : π ^ k * b - l * (π ^ k * a) = π ^ k * (b - l * a) := by ring
    rw [he, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπ k)
      (Ideal.sub_mem _ hb ((maximalIdeal A).mul_mem_right a hlm))
  have hνj : ν = t - l * z := by dsimp [ν]; linear_combination -hline
  have hνr : ν = π ^ u.depth * u.b - l * (π ^ u.depth * u.a) := hν3.symm
  have hνsq := node_line_intercept_square_mem D v.depth w.depth u.depth (by omega)
    (by omega) x z (π ^ u.depth * u.a) l ν (hmem _ _) (hmem _ _) (hmem _ _) hlm
    (hint _ _ _ hb) (hνj ▸ hint _ _ _ hd) (hνr ▸ hint _ _ _ hf) hpair
  have hunit {T : (W.map (algebraMap A K)).toProjective.Point}
      (a : NodePointCoordinates A W π T) (ha : 0 < a.depth) (han : 2 * a.depth < n) :
      IsUnit a.a := (node_point_branches_below_middle W D.uniformizer_ne_zero D.maximalIdeal_eq
        n a.depth ha han D.a₁_unit D.a₂_mem D.a₃_mem D.a₄_mem D.a₆_mem
        a.a a.b a.primitive a.equation).1
  exact node_triple_depth_eq D v.depth w.depth u.depth v.a w.a u.a ν
    (hunit v hk (by omega)) (hunit w (by omega) hw) (hunit u hu hun) hνsq hprod

end FLT.Mazur
