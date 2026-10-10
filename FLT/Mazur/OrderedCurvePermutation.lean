/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedCurveDivisorPullback

/-!
# Permutations of ordered points preserve the universal divisor

Permuting coordinates gives actual automorphisms of the parameter scheme. On the
universal curve, the actual divisor ideal is invariant under the induced map.
This is symmetry of the ordered family, not construction of its scheme quotient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.OrderedCurvePower

variable {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ)

/-- Reindex the universal ordered tuple by a permutation. -/
def reindex (σ : Equiv.Perm (Fin n)) : space f n ⟶ space f n :=
  classify f n (base f n) (fun i ↦ point f n (σ i)) (fun i ↦ point_base f n (σ i))

@[reassoc (attr := simp)]
lemma reindex_point (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    reindex f n σ ≫ point f n i = point f n (σ i) := classify_point _ _ _ _ _ _

@[reassoc (attr := simp)]
lemma reindex_base (σ : Equiv.Perm (Fin n)) :
    reindex f n σ ≫ base f n = base f n := classify_base _ _ _ _ _

/-- Reindexing by the identity fixes the actual parameter scheme. -/
@[simp]
lemma reindex_refl : reindex f n (Equiv.refl _) = 𝟙 _ := by
  apply hom_ext <;> simp

/-- Composition is the contravariant composition of coordinate permutations. -/
lemma reindex_comp (σ τ : Equiv.Perm (Fin n)) :
    reindex f n σ ≫ reindex f n τ = reindex f n (τ.trans σ) := by
  apply hom_ext <;> simp

/-- The inverse permutation constructs an actual scheme automorphism. -/
def reindexIso (σ : Equiv.Perm (Fin n)) : space f n ≅ space f n where
  hom := reindex f n σ
  inv := reindex f n σ.symm
  hom_inv_id := by apply hom_ext <;> simp
  inv_hom_id := by apply hom_ext <;> simp

/-- The induced reindexing map of the actual universal curve. -/
def reindexCurve (σ : Equiv.Perm (Fin n)) : curve f n ⟶ curve f n :=
  CurveGraphPullback.curveMap f (base f n) (base f n) (reindex f n σ)
    (reindex_base f n σ)

/-- A permuted tuple has exactly the same ideal product, including multiplicities. -/
theorem divisorIdeal_reindex_comap [IsSeparated f] (σ : Equiv.Perm (Fin n)) :
    (divisorIdeal f n).comap (reindexCurve f n σ) = divisorIdeal f n := by
  change (divisorIdeal f n).comap
    (classifyingCurveMap f n (base f n) (fun i ↦ point f n (σ i))
      (fun i ↦ point_base f n (σ i))) = _
  rw [divisorIdeal_classifying_comap]
  change (∏ i : Fin n, (graph f n (σ i)).ker) = ∏ i : Fin n, (graph f n i).ker
  exact Equiv.prod_comp σ (fun i ↦ (graph f n i).ker)

end FLT.Mazur.OrderedCurvePower
