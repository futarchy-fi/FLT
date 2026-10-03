/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.PDivisibleTateSequences
public import Mathlib.Order.KonigLemma

/-! # Surjective evaluations of finite Tate towers

A prescribed point is lifted by applying the finite inverse-system theorem
to its fibers. The hypothesis concerns only the actual finite reductions.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Composition of the prescribed reductions on geometric points. -/
theorem pointReduction_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
    (x : (X.level n).Points) :
    genericHom (X.reduction h) (genericHom (X.reduction k) x) =
      genericHom (X.reduction (h.trans k)) x := by
  rw [← genericHom_comp, X.reduction_comp]

/-- Surjective finite reductions give surjective limit evaluations. -/
theorem tateEval_surjective
    (hs : ∀ {m n} (h : m ≤ n), Function.Surjective (genericHom (X.reduction h)))
    (n : ℕ) : Function.Surjective (X.tateEval n) := by
  intro a
  let F (k : ℕ) := {x : (X.level (n + k)).Points //
    genericHom (X.reduction (Nat.le_add_right n k)) x = a}
  have (k : ℕ) : Nonempty (F k) := by
    obtain ⟨x, hx⟩ := hs (Nat.le_add_right n k) a
    exact ⟨x, hx⟩
  let π {i j : ℕ} (h : i ≤ j) (x : F j) : F i :=
    ⟨genericHom (X.reduction (Nat.add_le_add_left h n)) x.val, by
      rw [X.pointReduction_comp]; exact x.property⟩
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite π
    (by intro i x; apply Subtype.ext; change genericHom (X.reduction _) x.val = x.val
        rw [X.reduction_refl, genericHom_id])
    (by intro i j k h k' x; apply Subtype.ext; exact X.pointReduction_comp _ _ _)
    (fun _ _ ↦ Set.toFinite _)
  let x (m : ℕ) : (X.level m).Points :=
    genericHom (X.reduction (Nat.le_add_left m n)) (f m).val
  have hx {m k : ℕ} (h : m ≤ k) : genericHom (X.reduction h) (x k) = x m := by
    have he := congrArg Subtype.val (hf h)
    change genericHom (X.reduction (Nat.add_le_add_left h n)) (f k).val = (f m).val at he
    dsimp [x]
    rw [X.pointReduction_comp, ← he, X.pointReduction_comp]
  refine ⟨⟨x, fun h ↦ hx h⟩, ?_⟩
  exact (f n).property

end ThreeAdicPlan.PDivisibleSystem
