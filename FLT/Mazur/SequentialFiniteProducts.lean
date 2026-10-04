/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin

/-!
# Common stages for finitely many local sections

Coordinatewise finite-stage lifting and kernel annihilation have one common
stage for a finite family. No finite generation of the groups is required.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace FLT.Mazur.SequentialFiniteProducts

variable {ι : Type u} [Finite ι] (F G : ι → ℕ ⥤ AddCommGrpCat.{v})
  (a : ∀ i, F i ⟶ G i)

/-- Finitely many local lifts can be transported to one common stage. -/
theorem common_stage_lift
    (hLift : ∀ i n (b : (G i).obj n), ∃ (m : ℕ) (h : n ≤ m) (c : (F i).obj m),
      (a i).app m c = (G i).map (homOfLE h) b)
    (n : ℕ) (b : ∀ i, (G i).obj n) :
    ∃ (m : ℕ) (h : n ≤ m) (c : ∀ i, (F i).obj m),
      ∀ i, (a i).app m (c i) = (G i).map (homOfLE h) (b i) := by
  classical
  let := Fintype.ofFinite ι
  choose m hm c hc using fun i ↦ hLift i n (b i)
  let l := max n (Finset.univ.sup m)
  have hnl : n ≤ l := le_max_left _ _
  have hml (i : ι) : m i ≤ l :=
    (Finset.le_sup (f := m) (Finset.mem_univ i)).trans (le_max_right _ _)
  refine ⟨l, hnl, fun i ↦ (F i).map (homOfLE (hml i)) (c i), fun i ↦ ?_⟩
  change ((F i).map (homOfLE (hml i)) ≫ (a i).app l) (c i) = _
  rw [(a i).naturality]
  change (G i).map (homOfLE (hml i)) ((a i).app (m i) (c i)) = _
  rw [hc i, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Finitely many elements in restriction kernels die at one common stage. -/
theorem common_stage_annihilator
    (hKill : ∀ i n (x : (F i).obj n), (a i).app n x = 0 →
      ∃ (m : ℕ) (h : n ≤ m), (F i).map (homOfLE h) x = 0)
    (n : ℕ) (x : ∀ i, (F i).obj n) (hx : ∀ i, (a i).app n (x i) = 0) :
    ∃ (m : ℕ) (h : n ≤ m), ∀ i, (F i).map (homOfLE h) (x i) = 0 := by
  classical
  let := Fintype.ofFinite ι
  choose m hm hz using fun i ↦ hKill i n (x i) (hx i)
  let l := max n (Finset.univ.sup m)
  have hnl : n ≤ l := le_max_left _ _
  have hml (i : ι) : m i ≤ l :=
    (Finset.le_sup (f := m) (Finset.mem_univ i)).trans (le_max_right _ _)
  refine ⟨l, hnl, fun i ↦ ?_⟩
  have he : homOfLE hnl = homOfLE (hm i) ≫ homOfLE (hml i) := rfl
  rw [he, Functor.map_comp, ConcreteCategory.comp_apply, hz i, map_zero]

end FLT.Mazur.SequentialFiniteProducts
