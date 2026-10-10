/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteIteration

/-!
# A finite open atlas for the actual iterated modification

At stage j the enlarged exterior is covered by the retained initial exterior
and j actual successive x-direction charts. Adding the actual final divided
chart gives a finite open cover of the whole constructed scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (E : Exterior (data ⟨0, Nat.zero_lt_succ n⟩))

/-- The retained original exterior and all actual successive x-charts. -/
def finiteExteriorAtlasObject : (j : ℕ) → (hj : j ≤ n) → Fin (j + 1) → Scheme
  | 0, _, _ => E.carrier
  | j + 1, hj, i => Fin.cases (stepX (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (finiteExteriorAtlasObject j (Nat.le_of_succ_le hj)) i

/-- Each original equation chart embeds into the recursively enlarged exterior. -/
def finiteExteriorAtlasMap : (j : ℕ) → (hj : j ≤ n) → (i : Fin (j + 1)) →
    finiteExteriorAtlasObject data E j hj i ⟶ (finiteExterior hπ data E j hj).carrier
  | 0, _, _ => 𝟙 _
  | j + 1, hj, i => Fin.cases
    ((finiteExterior hπ data E j (Nat.le_of_succ_le hj)).newX hπ
      (data ⟨j + 1, Nat.lt_succ_of_le hj⟩))
    (fun a => finiteExteriorAtlasMap j (Nat.le_of_succ_le hj) a ≫
      (finiteExterior hπ data E j (Nat.le_of_succ_le hj)).retained hπ
        (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)) i

instance finiteExteriorAtlasMap_isOpenImmersion (j : ℕ) (hj : j ≤ n) (i : Fin (j + 1)) :
    IsOpenImmersion (finiteExteriorAtlasMap hπ data E j hj i) := by
  induction j with
  | zero => change IsOpenImmersion (𝟙 E.carrier); infer_instance
  | succ j ih =>
    cases i using Fin.cases with
    | zero => dsimp only [finiteExteriorAtlasMap, Fin.cases_zero]; infer_instance
    | succ i =>
      let _ := ih (Nat.le_of_succ_le hj) i
      dsimp only [finiteExteriorAtlasMap, Fin.cases_succ]
      infer_instance

/-- These finitely many charts cover the enlarged exterior. -/
theorem finiteExteriorAtlas_cover (j : ℕ) (hj : j ≤ n)
    (z : (finiteExterior hπ data E j hj).carrier) :
    ∃ i a, finiteExteriorAtlasMap hπ data E j hj i a = z := by
  induction j with
  | zero => exact ⟨0, z, rfl⟩
  | succ j ih =>
    rcases (finiteExterior hπ data E j (Nat.le_of_succ_le hj)).advance_cover hπ
      (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) z with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · obtain ⟨i, b, rfl⟩ := ih (Nat.le_of_succ_le hj) a
      exact ⟨i.succ, b, rfl⟩
    · exact ⟨0, a, rfl⟩

/-- Add the actual final divided equation chart to the finite exterior atlas. -/
def finiteAtlasObject (j : ℕ) (hj : j ≤ n) : Fin (j + 2) → Scheme :=
  Fin.cases (chart (data ⟨j, Nat.lt_succ_of_le hj⟩)) (finiteExteriorAtlasObject data E j hj)

/-- The finite atlas maps into the actual whole scheme. -/
def finiteAtlasMap (j : ℕ) (hj : j ≤ n) (i : Fin (j + 2)) :
    finiteAtlasObject data E j hj i ⟶ finiteWhole hπ data E j hj :=
  Fin.cases (finiteExterior hπ data E j hj).dividedChart
    (fun a => finiteExteriorAtlasMap hπ data E j hj a ≫
      (finiteExterior hπ data E j hj).exteriorChart) i

instance finiteAtlasMap_isOpenImmersion (j : ℕ) (hj : j ≤ n) (i : Fin (j + 2)) :
    IsOpenImmersion (finiteAtlasMap hπ data E j hj i) := by
  cases i using Fin.cases with
  | zero => dsimp only [finiteAtlasMap, Fin.cases_zero]; infer_instance
  | succ i => dsimp only [finiteAtlasMap, Fin.cases_succ]; infer_instance

/-- The finite atlas covers the actual whole scheme. -/
theorem finiteAtlas_cover (j : ℕ) (hj : j ≤ n) (z : finiteWhole hπ data E j hj) :
    ∃ i a, finiteAtlasMap hπ data E j hj i a = z := by
  rcases (finiteExterior hπ data E j hj).charts_cover z with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · obtain ⟨i, b, rfl⟩ := finiteExteriorAtlas_cover hπ data E j hj a
    exact ⟨i.succ, b, rfl⟩
  · exact ⟨0, a, rfl⟩

/-- Package the finitely many actual charts as an open cover of the whole scheme. -/
def finiteOpenCover (j : ℕ) (hj : j ≤ n) : (finiteWhole hπ data E j hj).OpenCover where
  I₀ := Fin (j + 2)
  X := finiteAtlasObject data E j hj
  f := finiteAtlasMap hπ data E j hj
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨finiteAtlas_cover hπ data E j hj,
      fun i => finiteAtlasMap_isOpenImmersion hπ data E j hj i⟩

omit [IsDomain R] in
instance finiteExteriorAtlasObject_isAffine [IsAffine E.carrier]
    (j : ℕ) (hj : j ≤ n) (i : Fin (j + 1)) :
    IsAffine (finiteExteriorAtlasObject data E j hj i) := by
  induction j with
  | zero => exact inferInstanceAs (IsAffine E.carrier)
  | succ j ih =>
    cases i using Fin.cases with
    | zero => dsimp only [finiteExteriorAtlasObject, Fin.cases_zero, stepX]; infer_instance
    | succ i => exact ih (Nat.le_of_succ_le hj) i

omit [IsDomain R] in
instance finiteAtlasObject_isAffine [IsAffine E.carrier]
    (j : ℕ) (hj : j ≤ n) (i : Fin (j + 2)) : IsAffine (finiteAtlasObject data E j hj i) := by
  cases i using Fin.cases with
  | zero => dsimp only [finiteAtlasObject, Fin.cases_zero, chart]; infer_instance
  | succ i => exact finiteExteriorAtlasObject_isAffine data E j hj i

end FLT.Mazur.WeierstrassDividedDepth
