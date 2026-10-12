/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedShearExterior
public import FLT.Mazur.WeierstrassDividedFiniteIteration

/-!
# Shear comparison through every finite exterior iteration

Starting with an exterior isomorphism over its actual boundary, recursively
construct the comparison on every original enlarged exterior and whole scheme.
The recursion retains each original successive contraction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (r : R)
  (E : Exterior (data ⟨0, Nat.zero_lt_succ n⟩))
  (F : Exterior (shearData (data ⟨0, Nat.zero_lt_succ n⟩) r))
  (i : F.carrier ≅ E.carrier)
  (hi : F.attach ≫ i.hom = (shearBoundaryIso (data ⟨0, Nat.zero_lt_succ n⟩) r).hom ≫ E.attach)
local notation "dat" => fun a => shearData (data a) r
local notation "EE" => finiteExterior hπ data E
local notation "FF" => finiteExterior hπ dat F

/-- Construct the full finite exterior isomorphism together with its actual attachment square. -/
def finiteExteriorShearComparison : (j : ℕ) → (hj : j ≤ n) →
    { f : (FF j hj).carrier ≅ (EE j hj).carrier //
      (FF j hj).attach ≫ f.hom =
        (shearBoundaryIso (data ⟨j, Nat.lt_succ_of_le hj⟩) r).hom ≫ (EE j hj).attach }
  | 0, _ => ⟨i, hi⟩
  | j + 1, hj =>
    let prev := finiteExteriorShearComparison j (Nat.le_of_succ_le hj)
    ⟨shearAdvanceIso r (EE j (Nat.le_of_succ_le hj)) (FF j (Nat.le_of_succ_le hj))
      prev.val prev.property hπ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩),
      shearAdvanceIso_attach r (EE j (Nat.le_of_succ_le hj)) (FF j (Nat.le_of_succ_le hj))
        prev.val prev.property hπ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)⟩

/-- The actual comparison on the entire finite enlarged exterior. -/
def finiteExteriorShearIso (j : ℕ) (hj : j ≤ n) : (FF j hj).carrier ≅ (EE j hj).carrier :=
  (finiteExteriorShearComparison hπ data r E F i hi j hj).val

/-- Every recursively constructed comparison retains its original deeper attachment. -/
@[reassoc] theorem finiteExteriorShearIso_attach (j : ℕ) (hj : j ≤ n) :
    (FF j hj).attach ≫ (finiteExteriorShearIso hπ data r E F i hi j hj).hom =
      (shearBoundaryIso (data ⟨j, Nat.lt_succ_of_le hj⟩) r).hom ≫ (EE j hj).attach :=
  (finiteExteriorShearComparison hπ data r E F i hi j hj).property

/-- Glue the constructed exterior comparison to the actual final divided chart. -/
def finiteWholeShearIso (j : ℕ) (hj : j ≤ n) :
    finiteWhole hπ dat F j hj ≅ finiteWhole hπ data E j hj :=
  shearWholeIso r (EE j hj) (FF j hj) (finiteExteriorShearIso hπ data r E F i hi j hj)
    (finiteExteriorShearIso_attach hπ data r E F i hi j hj)

/-- The finite whole comparison retains the complete original enlarged exterior. -/
@[reassoc] theorem finiteWholeShearIso_exterior (j : ℕ) (hj : j ≤ n) :
    (FF j hj).exteriorChart ≫ (finiteWholeShearIso hπ data r E F i hi j hj).hom =
      (finiteExteriorShearIso hπ data r E F i hi j hj).hom ≫ (EE j hj).exteriorChart :=
  shearWholeIso_exterior _ _ _ _ _

/-- The finite whole comparison retains the complete original final divided chart. -/
@[reassoc] theorem finiteWholeShearIso_divided (j : ℕ) (hj : j ≤ n) :
    (FF j hj).dividedChart ≫ (finiteWholeShearIso hπ data r E F i hi j hj).hom =
      (shearChartIso (data ⟨j, Nat.lt_succ_of_le hj⟩) r).hom ≫ (EE j hj).dividedChart :=
  shearWholeIso_divided _ _ _ _ _

/-- Every original single-step whole contraction commutes with the constructed shear. -/
@[reassoc] theorem finiteWholeShearIso_step (j : ℕ) (hj : j + 1 ≤ n) :
    (finiteWholeShearIso hπ data r E F i hi (j + 1) hj).hom ≫ finiteStep hπ data E j hj =
      finiteStep hπ dat F j hj ≫
        (finiteWholeShearIso hπ data r E F i hi j (Nat.le_of_succ_le hj)).hom :=
  shearAdvanceWholeIso_step r (EE j (Nat.le_of_succ_le hj)) (FF j (Nat.le_of_succ_le hj))
    (finiteExteriorShearIso hπ data r E F i hi j (Nat.le_of_succ_le hj))
    (finiteExteriorShearIso_attach hπ data r E F i hi j (Nat.le_of_succ_le hj))
    hπ (data ⟨j + 1, Nat.lt_succ_of_le hj⟩)

/-- The entire finite contraction to the initial whole is preserved. -/
@[reassoc] theorem finiteWholeShearIso_contraction (j : ℕ) (hj : j ≤ n) :
    (finiteWholeShearIso hπ data r E F i hi j hj).hom ≫ finiteContraction hπ data E j hj =
      finiteContraction hπ dat F j hj ≫ (shearWholeIso r E F i hi).hom := by
  induction j with
  | zero => simp only [finiteContraction, Category.comp_id, Category.id_comp]; rfl
  | succ j ih =>
    rw [finiteContraction, finiteWholeShearIso_step_assoc,
      ih (Nat.le_of_succ_le hj), finiteContraction, Category.assoc]

/-- The comparison retains the original initial exterior at every finite stage. -/
@[reassoc] theorem finiteExteriorShearIso_retained (j : ℕ) (hj : j ≤ n) :
    finiteRetained hπ dat F j hj ≫ (finiteExteriorShearIso hπ data r E F i hi j hj).hom =
      i.hom ≫ finiteRetained hπ data E j hj := by
  induction j with
  | zero => simp only [finiteRetained, Category.id_comp, Category.comp_id]; rfl
  | succ j ih =>
    change (finiteRetained hπ dat F j (Nat.le_of_succ_le hj) ≫
      (FF j (Nat.le_of_succ_le hj)).retained hπ _) ≫
        (shearAdvanceIso r _ _ _ _ hπ _).hom = _
    rw [Category.assoc, shearAdvanceIso_retained, ← Category.assoc]
    erw [ih (Nat.le_of_succ_le hj), Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
