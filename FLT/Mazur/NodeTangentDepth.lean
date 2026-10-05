/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NodeTangentShear
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Exact nodal depth survives the unramified tangent extension

The monic root algebra is free and faithful. Its maximal ideal is the extension
of the original maximal ideal, so all maximal-ideal powers both ascend and
descend. Shearing by the tangent root therefore supplies `SplitNodeDepth` at
the original exact depth.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {R : Type*} [CommRing R] [IsLocalRing R]
  (W : WeierstrassCurve R)

/-- The tangent root algebra is local when its residue polynomial is irreducible. -/
theorem nodeTangentAlgebra_isLocalRing
    (hirr : Irreducible ((nodeTangentPolynomial W).map (residue R))) :
    IsLocalRing (AdjoinRoot (nodeTangentPolynomial W)) := by
  let : Module.Finite R (AdjoinRoot (nodeTangentPolynomial W)) :=
    (nodeTangentPolynomial_monic W).finite_adjoinRoot
  exact IsLocalRing.of_isMaximal_map_maximalIdeal
    (AdjoinRoot.isMaximal_map_maximalIdeal hirr)

variable [IsLocalRing (AdjoinRoot (nodeTangentPolynomial W))]

/-- The nonsplit tangent extension has ramification index one at the ideal level. -/
theorem nodeTangentAlgebra_maximalIdeal
    (hirr : Irreducible ((nodeTangentPolynomial W).map (residue R))) :
    maximalIdeal (AdjoinRoot (nodeTangentPolynomial W)) =
      (maximalIdeal R).map (algebraMap R _) :=
  (IsLocalRing.eq_maximalIdeal (AdjoinRoot.isMaximal_map_maximalIdeal hirr)).symm

/-- Every maximal-ideal depth is preserved and reflected by the tangent extension. -/
theorem nodeTangentAlgebra_mem_maximalIdeal_pow_iff
    (hirr : Irreducible ((nodeTangentPolynomial W).map (residue R))) (x : R) (n : ℕ) :
    algebraMap R (AdjoinRoot (nodeTangentPolynomial W)) x ∈
        maximalIdeal (AdjoinRoot (nodeTangentPolynomial W)) ^ n ↔
      x ∈ maximalIdeal R ^ n := by
  let : Nontrivial (AdjoinRoot (nodeTangentPolynomial W)) :=
    Module.nontrivial_of_finrank_pos (by rw [nodeTangentAlgebra_finrank]; decide)
  let : Module.Free R (AdjoinRoot (nodeTangentPolynomial W)) :=
    (nodeTangentPolynomial_monic W).free_adjoinRoot
  rw [nodeTangentAlgebra_maximalIdeal W hirr, ← Ideal.map_pow]
  change x ∈ Ideal.comap (algebraMap R _) ((maximalIdeal R ^ n).map (algebraMap R _)) ↔ _
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat]

/-- A finite-depth nonsplit equation becomes an actual split finite-depth equation over
its quadratic tangent algebra, with the original uniformizer and exact depth. -/
theorem nodeTangentShear_splitNodeDepth [IsDomain R]
    (hirr : Irreducible ((nodeTangentPolynomial W).map (residue R)))
    {π : R} {n : ℕ} (hn : 0 < n) (hπ0 : π ≠ 0)
    (hπ : maximalIdeal R = Ideal.span {π}) (hb : IsUnit W.b₂)
    (h3 : W.a₃ ∈ maximalIdeal R ^ (n + 1))
    (h4 : W.a₄ ∈ maximalIdeal R ^ (n + 1))
    (h6 : W.a₆ ∈ maximalIdeal R ^ n)
    (h6' : W.a₆ ∉ maximalIdeal R ^ (n + 1)) :
    SplitNodeDepth (nodeTangentShear W) (algebraMap R _ π) n := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄, ha₆⟩ := nodeTangentShear_coefficients W
  have hi : Function.Injective (algebraMap R (AdjoinRoot (nodeTangentPolynomial W))) := by
    rw [AdjoinRoot.algebraMap_eq]
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [nodeTangentPolynomial_degree]
    norm_num
  have hm := nodeTangentAlgebra_mem_maximalIdeal_pow_iff W hirr
  refine ⟨hn, fun hz => hπ0 (hi (by simpa using hz)), ?_,
    nodeTangentShear_a₁_isUnit W hb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nodeTangentAlgebra_maximalIdeal W hirr, hπ, Ideal.map_span, Set.image_singleton]
  · rw [ha₂]
    exact Ideal.zero_mem _
  · rw [ha₃]
    exact (hm _ _).mpr h3
  · rw [ha₄]
    exact Ideal.sub_mem _ ((hm _ _).mpr h4) (Ideal.mul_mem_left _ _ ((hm _ _).mpr h3))
  · rw [ha₆]
    exact (hm _ _).mpr h6
  · rw [ha₆]
    exact fun h => h6' ((hm _ _).mp h)

end FLT.Mazur
