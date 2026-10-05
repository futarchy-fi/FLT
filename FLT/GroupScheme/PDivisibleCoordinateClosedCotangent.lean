/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleCoordinateParameters
public import FLT.GroupScheme.PDivisibleCoordinateTopology

/-! # The original cotangent limit and the closed square of the augmentation ideal -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Evaluation maps the original augmentation ideal onto the original finite ideal. -/
theorem coordinateAugmentationIdeal_map (n : ℕ) :
    X.coordinateAugmentationIdeal.map (X.coordinateEval n) = (X.level n).cotangentIdeal := by
  ext a
  rw [Ideal.mem_map_iff_of_surjective _ (X.coordinateEval_surjective n)]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (X.coordinateAugmentation_eval n x).trans hx
  · intro ha
    obtain ⟨x, hx⟩ := X.coordinateAugmentationEval_surjective n ⟨a, ha⟩
    exact ⟨x.val, x.property, congrArg Subtype.val hx⟩

/-- Finite evaluations detect the closure of every power of the original augmentation ideal. -/
theorem mem_closure_coordinateAugmentationIdeal_pow_iff (r : ℕ) (x : X.coordinateLimit) :
    x ∈ closure (↑(X.coordinateAugmentationIdeal ^ r) : Set X.coordinateLimit) ↔
      ∀ n, X.coordinateEval n x ∈ (X.level n).cotangentIdeal ^ r := by
  have hmap (n : ℕ) : (X.coordinateAugmentationIdeal ^ r).map (X.coordinateEval n) =
      (X.level n).cotangentIdeal ^ r := by
    rw [Ideal.map_pow, X.coordinateAugmentationIdeal_map]
  constructor
  · intro hx n
    obtain ⟨y, hy, hy'⟩ := mem_closure_iff.mp hx _ (X.coordinateEval_fiber_isOpen n
      (X.coordinateEval n x)) rfl
    rw [← hmap]
    exact (Ideal.mem_map_iff_of_surjective _ (X.coordinateEval_surjective n)).mpr
      ⟨y, hy', hy⟩
  · intro hx
    apply mem_closure_iff.mpr
    intro U hU hxU
    obtain ⟨n, hn⟩ := X.coordinateEval_fiber_basis hU x hxU
    have hx' := hx n
    rw [← hmap n, Ideal.mem_map_iff_of_surjective _ (X.coordinateEval_surjective n)] at hx'
    obtain ⟨y, hy, he⟩ := hx'
    exact ⟨y, hn he, hy⟩

/-- The kernel of the original derivative is exactly the closed augmentation square. -/
theorem coordinateCotangent_eq_zero_iff_mem_closure (x : X.coordinateAugmentationIdeal) :
    X.coordinateCotangent x = 0 ↔
      x.val ∈ closure (↑(X.coordinateAugmentationIdeal ^ 2) : Set X.coordinateLimit) :=
  (X.coordinateCotangent_eq_zero_iff x).trans
    (X.mem_closure_coordinateAugmentationIdeal_pow_iff 2 x.val).symm

end ThreeAdicPlan.PDivisibleSystem
