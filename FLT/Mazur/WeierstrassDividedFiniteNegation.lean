/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialExteriorNegation
public import FLT.Mazur.WeierstrassDividedExteriorNegationStep
public import FLT.Mazur.WeierstrassDividedFiniteIteration

/-!
# Constructed negatives at every actual finite local stage

Start with the original incidence reflection and iterate the proved exterior
extension. Every finite whole model receives a constructed involution, and
every actual successor contraction is retained. No negative is supplied as data.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
local notation "E₀" => initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)
local notation "E" => finiteExterior hπ data E₀

/-- Recursively construct every exterior negative and prove its boundary compatibility. -/
def finiteExteriorNegationData : (j : ℕ) → (hj : j ≤ n) →
    { N : (E j hj).carrier ≅ (E j hj).carrier //
      (boundaryNegationIso (data ⟨j, Nat.lt_succ_of_le hj⟩)).hom ≫ (E j hj).attach =
        (E j hj).attach ≫ N.hom }
  | 0, _ => ⟨initialExteriorNegationIso _, initialExteriorNegationIso_attach _ hπ⟩
  | j + 1, hj =>
    let prev := finiteExteriorNegationData j (Nat.le_of_succ_le hj)
    ⟨(E j (Nat.le_of_succ_le hj)).advanceNegationIso hπ
        (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) prev.val prev.property,
      (E j (Nat.le_of_succ_le hj)).advanceNegationIso_attach hπ
        (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) prev.val prev.property⟩

/-- The actual exterior automorphism at any available finite stage. -/
def finiteExteriorNegationIso (j : ℕ) (hj : j ≤ n) : (E j hj).carrier ≅ (E j hj).carrier :=
  (finiteExteriorNegationData hπ data j hj).val

/-- Every constructed finite exterior negative keeps its exact attachment map. -/
@[reassoc] theorem finiteExteriorNegationIso_attach (j : ℕ) (hj : j ≤ n) :
    (boundaryNegationIso (data ⟨j, Nat.lt_succ_of_le hj⟩)).hom ≫ (E j hj).attach =
      (E j hj).attach ≫ (finiteExteriorNegationIso hπ data j hj).hom :=
  (finiteExteriorNegationData hπ data j hj).property

/-- The negative on the whole actual finite local model, including all earlier components. -/
def finiteWholeNegationIso (j : ℕ) (hj : j ≤ n) :
    finiteWhole hπ data E₀ j hj ≅ finiteWhole hπ data E₀ j hj :=
  (E j hj).wholeNegationIso (finiteExteriorNegationIso hπ data j hj)
    (finiteExteriorNegationIso_attach hπ data j hj)

/-- Every finite whole negative retains its entire actual exterior. -/
@[reassoc] theorem finiteWholeNegationIso_exterior (j : ℕ) (hj : j ≤ n) :
    (E j hj).exteriorChart ≫ (finiteWholeNegationIso hπ data j hj).hom =
      (finiteExteriorNegationIso hπ data j hj).hom ≫ (E j hj).exteriorChart :=
  Exterior.exteriorChart_wholeNegationIso _ _ _

/-- Every finite whole negative retains the actual final divided chart. -/
@[reassoc] theorem finiteWholeNegationIso_divided (j : ℕ) (hj : j ≤ n) :
    (E j hj).dividedChart ≫ (finiteWholeNegationIso hπ data j hj).hom =
      (chartNegationIso (data ⟨j, Nat.lt_succ_of_le hj⟩)).hom ≫ (E j hj).dividedChart :=
  Exterior.dividedChart_wholeNegationIso _ _ _

/-- The recursively constructed negative is involutive on each entire exterior. -/
@[reassoc] theorem finiteExteriorNegationIso_comp (j : ℕ) (hj : j ≤ n) :
    (finiteExteriorNegationIso hπ data j hj).hom ≫
      (finiteExteriorNegationIso hπ data j hj).hom = 𝟙 _ := by
  induction j with
  | zero => exact initialExteriorNegationIso_comp _
  | succ j ih =>
    exact Exterior.advanceNegationIso_comp hπ (E j (Nat.le_of_succ_le hj))
      (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)
      (finiteExteriorNegationIso hπ data j (Nat.le_of_succ_le hj))
      (finiteExteriorNegationIso_attach hπ data j (Nat.le_of_succ_le hj))
      (ih (Nat.le_of_succ_le hj))

/-- The constructed negative is involutive on every entire finite local model. -/
@[reassoc] theorem finiteWholeNegationIso_comp (j : ℕ) (hj : j ≤ n) :
    (finiteWholeNegationIso hπ data j hj).hom ≫
      (finiteWholeNegationIso hπ data j hj).hom = 𝟙 _ :=
  Exterior.wholeNegationIso_comp _ _ _ (finiteExteriorNegationIso_comp hπ data j hj)

/-- Every actual finite successor contraction commutes with the constructed negatives. -/
@[reassoc] theorem finiteWholeNegationIso_step (j : ℕ) (hj : j + 1 ≤ n) :
    (finiteWholeNegationIso hπ data (j + 1) hj).hom ≫ finiteStep hπ data E₀ j hj =
      finiteStep hπ data E₀ j hj ≫
        (finiteWholeNegationIso hπ data j (Nat.le_of_succ_le hj)).hom :=
  Exterior.wholeNegationIso_step hπ (E j (Nat.le_of_succ_le hj))
    (data ⟨j + 1, Nat.lt_succ_of_le hj⟩) _ _

/-- Every finite composite retains the original initial whole model under negation. -/
@[reassoc] theorem finiteWholeNegationIso_contraction (j : ℕ) (hj : j ≤ n) :
    (finiteWholeNegationIso hπ data j hj).hom ≫ finiteContraction hπ data E₀ j hj =
      finiteContraction hπ data E₀ j hj ≫
        (finiteWholeNegationIso hπ data 0 (Nat.zero_le n)).hom := by
  induction j with
  | zero => simp only [finiteContraction, Category.comp_id, Category.id_comp]
  | succ j ih =>
    rw [finiteContraction, finiteWholeNegationIso_step_assoc, ih, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
