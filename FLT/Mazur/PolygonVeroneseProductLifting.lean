/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompatibleVeronese

/-!
# Homogeneous sums of original compatible products

Finite sums of products stay in their retained homogeneous degree. Their
insertion and every original stage evaluation retain precisely the given
products, allowing closed multiplication formulas to be lifted inside a
specified subalgebra.
-/

@[expose] public noncomputable section

open scoped DirectSum

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] compatibleEval

variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) (q : ℕ)
  {I : Type} [Fintype I] (a b : ℕ)

/-- Sums of compatible products lift their actual stage products inside the same subalgebra. -/
theorem compatibleVeronese_product_sum_lift
    (A : Subalgebra (PowerSeries R) (CompatibleVeroneseSections R n h q))
    (s : I → compatibleVeroneseDegree R n h q a)
    (t : I → compatibleVeroneseDegree R n h q b)
    (hs : ∀ i, (DirectSum.of _ a (s i) : CompatibleVeroneseSections R n h q) ∈ A)
    (ht : ∀ i, (DirectSum.of _ b (t i) : CompatibleVeroneseSections R n h q) ∈ A) :
    ∃ u : compatibleVeroneseDegree R n h q (a + b),
      (DirectSum.of _ (a + b) u : CompatibleVeroneseSections R n h q) ∈ A ∧
        ∀ m, compatibleEval R n h m u =
          ∑ i, compatibleEval R n h m (s i) * compatibleEval R n h m (t i) := by
  let u : compatibleVeroneseDegree R n h q (a + b) :=
    ∑ i, GradedMonoid.GMul.mul
      (A := fun d ↦ ↥(compatibleVeroneseDegree R n h q d)) (s i) (t i)
  have hu : (DirectSum.of _ (a + b) u : CompatibleVeroneseSections R n h q) =
      ∑ i, DirectSum.of _ a (s i) * DirectSum.of _ b (t i) := by
    simp only [u, map_sum, DirectSum.of_mul_of]
  refine ⟨u, ?_, fun m ↦ ?_⟩
  · rw [hu]
    exact A.sum_mem fun i _ ↦ A.mul_mem (hs i) (ht i)
  · have he := congrArg (compatibleVeroneseEval R n h q m) hu
    simpa only [map_sum, map_mul, compatibleVeroneseEval_of] using he

end FLT.Mazur.PolygonInfinitesimalStages
