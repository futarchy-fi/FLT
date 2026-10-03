/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedUniqueness
public import Mathlib.Data.PNat.Basic

/-!
# The degree-indexed tower of unramified stages

Each positive degree specifies a unique intermediate field. Containment is
divisibility, compositum corresponds to least common multiple, and the
resulting family is directed.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open IsLocalRing

variable (R K C : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [IsSepClosed C]
  [IsAdicComplete (maximalIdeal R) R]

/-- The unique unramified stage of positive degree `n` inside the chosen overfield. -/
def unramifiedStage (n : ℕ+) : IntermediateField K C :=
  (existsUnique_unramified_stage (R := R) (K := K) (C := C) (n : ℕ)).exists.choose

/-- The chosen stage has an actual unramified integral model. -/
theorem unramifiedStage_isUnramified (n : ℕ+) :
    IsUnramifiedStage R K (unramifiedStage R K C n) :=
  (existsUnique_unramified_stage (R := R) (K := K) (C := C) (n : ℕ)).exists.choose_spec.1

/-- Its fraction-field degree is the prescribed index. -/
@[simp] theorem finrank_unramifiedStage (n : ℕ+) :
    Module.finrank K (unramifiedStage R K C n) = n :=
  (existsUnique_unramified_stage (R := R) (K := K) (C := C) (n : ℕ)).exists.choose_spec.2

/-- Containment of stages is divisibility of their positive integer degrees. -/
theorem unramifiedStage_le_iff (n m : ℕ+) :
    unramifiedStage R K C n ≤ unramifiedStage R K C m ↔ (n : ℕ) ∣ m := by
  rw [(unramifiedStage_isUnramified R K C n).le_iff_finrank_dvd
    (unramifiedStage_isUnramified R K C m), finrank_unramifiedStage, finrank_unramifiedStage]

/-- The compositum of two stages is the stage of least common multiple degree. -/
theorem unramifiedStage_sup (n m : ℕ+) :
    unramifiedStage R K C n ⊔ unramifiedStage R K C m =
      unramifiedStage R K C ⟨Nat.lcm n m, Nat.lcm_pos n.pos m.pos⟩ := by
  let d : ℕ+ := ⟨Nat.lcm n m, Nat.lcm_pos n.pos m.pos⟩
  have hn : unramifiedStage R K C n ≤ unramifiedStage R K C d :=
    (unramifiedStage_le_iff R K C n d).mpr (Nat.dvd_lcm_left _ _)
  have hm : unramifiedStage R K C m ≤ unramifiedStage R K C d :=
    (unramifiedStage_le_iff R K C m d).mpr (Nat.dvd_lcm_right _ _)
  let := (unramifiedStage_isUnramified R K C n).1
  let := (unramifiedStage_isUnramified R K C m).1
  let := (unramifiedStage_isUnramified R K C d).1
  apply IntermediateField.eq_of_le_of_finrank_le (sup_le hn hm)
  rw [finrank_unramifiedStage]
  apply Nat.le_of_dvd Module.finrank_pos
  apply Nat.lcm_dvd
  · simpa only [finrank_unramifiedStage] using
      (IntermediateField.finrank_dvd_of_le_right
        (le_sup_left : unramifiedStage R K C n ≤
          unramifiedStage R K C n ⊔ unramifiedStage R K C m))
  · simpa only [finrank_unramifiedStage] using
      (IntermediateField.finrank_dvd_of_le_right
        (le_sup_right : unramifiedStage R K C m ≤
          unramifiedStage R K C n ⊔ unramifiedStage R K C m))

/-- The unramified stages form a directed system under inclusion. -/
theorem unramifiedStage_directed : Directed (· ≤ ·) (unramifiedStage R K C) := by
  intro n m
  refine ⟨⟨Nat.lcm n m, Nat.lcm_pos n.pos m.pos⟩, ?_, ?_⟩
  · exact (unramifiedStage_le_iff R K C _ _).mpr (Nat.dvd_lcm_left _ _)
  · exact (unramifiedStage_le_iff R K C _ _).mpr (Nat.dvd_lcm_right _ _)

/-- Every finite unramified intermediate field is one of the degree-indexed stages. -/
theorem IsUnramifiedStage.eq_unramifiedStage {E : IntermediateField K C}
    (hE : IsUnramifiedStage R K E) : ∃ n : ℕ+, E = unramifiedStage R K C n := by
  let := hE.1
  let n : ℕ+ := ⟨Module.finrank K E, Module.finrank_pos⟩
  exact ⟨n, hE.eq_of_finrank_eq (unramifiedStage_isUnramified R K C n)
    (finrank_unramifiedStage R K C n).symm⟩

end LocalClassFieldTheory
