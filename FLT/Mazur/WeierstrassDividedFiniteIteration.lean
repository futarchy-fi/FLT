/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorStep

/-!
# Arbitrary finite iteration with actual divided-depth data

A bounded family of coefficient factorizations constructs every exterior
and whole scheme up to its final depth. Each successor uses the actual local
replacement. The preceding whole contractions and retained exterior maps
compose to the initial stage; no infinite divisibility assumption is needed.
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

/-- The recursively enlarged exterior at every available finite depth. -/
def finiteExterior : (j : ℕ) → (hj : j ≤ n) → Exterior (data ⟨j, Nat.lt_succ_of_le hj⟩)
  | 0, _ => E
  | j + 1, hj =>
    (finiteExterior j (Nat.le_of_succ_le hj)).advance hπ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)

/-- The whole equation scheme at a finite stage. -/
def finiteWhole (j : ℕ) (hj : j ≤ n) : Scheme := (finiteExterior hπ data E j hj).whole

/-- The actual contraction from one whole stage to its predecessor. -/
def finiteStep (j : ℕ) (hj : j + 1 ≤ n) :
    finiteWhole hπ data E (j + 1) hj ⟶
      finiteWhole hπ data E j (Nat.le_of_succ_le hj) :=
  (finiteExterior hπ data E j (Nat.le_of_succ_le hj)).stepContraction hπ
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)

/-- Compose actual whole contractions down to the initial whole scheme. -/
def finiteContraction : (j : ℕ) → (hj : j ≤ n) → finiteWhole hπ data E j hj ⟶ E.whole
  | 0, _ => 𝟙 _
  | j + 1, hj => finiteStep hπ data E j hj ≫
    finiteContraction j (Nat.le_of_succ_le hj)

/-- The original exterior embeds in every recursively enlarged exterior. -/
def finiteRetained : (j : ℕ) → (hj : j ≤ n) →
    E.carrier ⟶ (finiteExterior hπ data E j hj).carrier
  | 0, _ => 𝟙 _
  | j + 1, hj => finiteRetained j (Nat.le_of_succ_le hj) ≫
    (finiteExterior hπ data E j (Nat.le_of_succ_le hj)).retained hπ
      (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)

instance finiteRetained_isOpenImmersion (j : ℕ) (hj : j ≤ n) :
    IsOpenImmersion (finiteRetained hπ data E j hj) := by
  induction j with
  | zero => change IsOpenImmersion (𝟙 E.carrier); infer_instance
  | succ j ih =>
    let _ := ih (Nat.le_of_succ_le hj)
    dsimp only [finiteRetained]
    infer_instance

/-- The original exterior is unchanged by every finite composite contraction. -/
@[reassoc] theorem finiteRetained_contraction (j : ℕ) (hj : j ≤ n) :
    finiteRetained hπ data E j hj ≫ (finiteExterior hπ data E j hj).exteriorChart ≫
        finiteContraction hπ data E j hj = E.exteriorChart := by
  induction j with
  | zero => simp [finiteRetained, finiteContraction, finiteWhole, finiteExterior]
  | succ j ih =>
    simp only [finiteRetained, finiteContraction, finiteStep, finiteExterior, Category.assoc,
      Exterior.exteriorChart_stepContraction_assoc, Exterior.retained_contraction_assoc]
    exact ih (Nat.le_of_succ_le hj)

end FLT.Mazur.WeierstrassDividedDepth
