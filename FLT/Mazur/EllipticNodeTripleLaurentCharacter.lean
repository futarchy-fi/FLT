/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeFirstTriple

/-!
# Leading coefficient of the first-branch triple product

The exact depth relation also determines the product of the primitive
horizontal residues. The error from the line intercept disappears one power
beyond that depth, leaving the negative normalized a₆ coefficient.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

/-- A deep error in a scaled product vanishes after cancelling the common depth. -/
theorem node_triple_product_residue {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
    (k j r : ℕ) (a c e ν c₆ : R) (hs : k + j + r = n)
    (h6 : W.a₆ = π ^ n * c₆) (hν : ν ^ 2 ∈ maximalIdeal R ^ (n + 1))
    (hp : (π ^ k * a) * (π ^ j * c) * (π ^ r * e) = ν ^ 2 + W.a₃ * ν - W.a₆) :
    residue R a * residue R c * residue R e = -residue R c₆ := by
  have hprod : (π ^ k * a) * (π ^ j * c) * (π ^ r * e) =
      π ^ n * (a * c * e) := by
    rw [← hs]
    simp only [pow_add]
    ring
  have he : π ^ n * (a * c * e + c₆) = ν ^ 2 + W.a₃ * ν := by
    rw [hprod, h6] at hp
    linear_combination hp
  have hm : a * c * e + c₆ ∈ maximalIdeal R := by
    apply node_factor_mem_maximalIdeal D.uniformizer_ne_zero D.maximalIdeal_eq n
    rw [he]
    exact Ideal.add_mem _ hν ((maximalIdeal R ^ (n + 1)).mul_mem_right ν D.a₃_mem)
  have hz := (residue_eq_zero_iff _).mpr hm
  rw [map_add, map_mul, map_mul] at hz
  linear_combination hz

variable {K : Type*} [Field K] {A : ValuationSubring K} {W : WeierstrassCurve A}
  {π : A} {n : ℕ} (D : SplitNodeDepth W π n)
  {P Q : (W.map (algebraMap A K)).toProjective.Point}

include D

/-- The original first-branch triple has the normalized a₆ leading coefficient. -/
theorem node_first_triple_horizontal_character
    (v : NodePointCoordinates A W π P) (w : NodePointCoordinates A W π Q)
    (u : NodePointCoordinates A W π (-(P + Q)))
    (hk : 0 < v.depth) (hkw : v.depth ≤ w.depth) (hw : 2 * w.depth < n)
    (hu : 0 < u.depth) (hun : 2 * u.depth < n)
    (hb : v.b ∈ maximalIdeal A) (hd : w.b ∈ maximalIdeal A) (hf : u.b ∈ maximalIdeal A) :
    ∀ c₆ : A, W.a₆ = π ^ n * c₆ →
      residue A v.a * residue A w.a * residue A u.a = -residue A c₆ := by
  intro c₆ h6
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
  have hs := node_depth_sum_of_first_triple D v w u hk hkw hw hu hun hb hd hf
  exact node_triple_product_residue D v.depth w.depth u.depth v.a w.a u.a ν c₆ hs
    h6 (by simpa only [hs] using hνsq) hprod

end FLT.Mazur
