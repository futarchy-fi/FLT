/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstResidualAtlas
public import FLT.Mazur.WeierstrassDividedFirstResidualIncoming
public import FLT.Mazur.WeierstrassDividedArithmeticPositiveEdgeCompatibility

/-!
# Unchanged first and adjacent arrows in the corrected complete atlas

The first edges retain their full original Laurent comparison even when
there is only one retained node. Every consecutive edge retains both of its
original normalized arrows. No tangent substitution enters these equations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π 1
local notation "t" => parameter R π 1
local notation "I" => changedArithmeticAtlasIso hπ data H 1 j hj u hu
local notation "κ" => changedArithmeticAtlasChart hπ data H 1 j hj u hu
local notation "ι" => arithmeticFirstResidualAtlasChart hπ data H j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H 1 j hj u hu
local notation "c" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj

/-- Every retained incoming inclusion remains exactly the original normalized one. -/
@[reassoc] theorem arithmeticFirstResidualAtlas_right (a : Fin (j + 1)) (b : Bool) :
    (rightBranchOpen Q t ≫ (I (.retained a b)).hom) ≫ ι (.retained a b) =
      rightBranchOpen Q t ≫ (I (.retained a b)).hom ≫ κ (.retained a b) := by
  simp only [arithmeticFirstResidualAtlasChart, arithmeticFirstResidualAtlasCorrection]
  split_ifs with ha
  · have h := arithmeticFirstResidualIncoming_oriented hπ data H j hj u hu a b
    have hi : (I (.retained a b)).hom =
        (arithmeticRetainedFixedSmoothingIso data H 1 (j + 1) hj a).hom ≫
          (twistedRetainedOrientation data H 1 b).hom := by
      simp only [changedArithmeticAtlasIso, twistedArithmeticAtlasIso,
        changedArithmeticAtlasToTwisted, Iso.trans_hom, Iso.symm_hom, Iso.refl_inv]
      exact Category.comp_id _
    rw [hi]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ κ (.retained a b)) h
  · simp only [Iso.refl_inv, Category.id_comp, Category.assoc]

/-- An outgoing edge below the last retained depth is unaffected. -/
@[reassoc] theorem arithmeticFirstResidualAtlas_left (a : Fin (j + 1))
    (ha : a.val < j) (b : Bool) :
    (leftBranchOpen Q t ≫ (I (.retained a b)).hom) ≫ ι (.retained a b) =
      leftBranchOpen Q t ≫ (I (.retained a b)).hom ≫ κ (.retained a b) := by
  simp only [arithmeticFirstResidualAtlasChart, arithmeticFirstResidualAtlasCorrection,
    ite_eq_right (show a.val ≠ j by omega), Iso.refl_inv, Category.id_comp, Category.assoc]

/-- The reciprocal incoming edge is also unchanged at every retained depth. -/
@[reassoc] theorem arithmeticFirstResidualAtlas_preceding (a : Fin (j + 1)) (b : Bool) :
    (precedingBranch Q t ≫ (I (.retained a b)).hom) ≫ ι (.retained a b) =
      precedingBranch Q t ≫ (I (.retained a b)).hom ≫ κ (.retained a b) := by
  simp only [precedingBranch, Category.assoc]
  rw [← Category.assoc (rightBranchOpen Q t), arithmeticFirstResidualAtlas_right]

/-- Every adjacent edge commutes using precisely the two unchanged normalized arrows. -/
@[reassoc] theorem arithmeticFirstResidualAtlas_adjacent
    (a : ℕ) (ha : a + 1 < j + 1) (b : Bool) :
    (leftBranchOpen Q t ≫ (I (.retained ⟨a, by omega⟩ b)).hom) ≫
        ι (.retained ⟨a, by omega⟩ b) =
      (precedingBranch Q t ≫ (I (.retained ⟨a + 1, ha⟩ b)).hom) ≫
        ι (.retained ⟨a + 1, ha⟩ b) := by
  rw [arithmeticFirstResidualAtlas_left hπ data H j hj u hu ⟨a, by omega⟩ (show a < j by omega) b,
    arithmeticFirstResidualAtlas_preceding, ← changedArithmeticAtlasIso_chart,
    ← changedArithmeticAtlasIso_chart, ← Category.assoc, ← Category.assoc,
    arithmeticLabeledAtlas_adjacent_overlap]

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => arithmeticInitialPunctureInclusion π 1 W (π ^ 1) H.a1_unit H.scale_div
local notation "E" => arithmeticInitialPunctureIso π 1 W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- Both original first edges remain unchanged, including the one-retained-node case. -/
@[reassoc] theorem arithmeticFirstResidualAtlas_initial (b : Bool) :
    P ≫ ι (.initial b) =
      ((E).inv ≫ rightBranchOpen Q t ≫
        (I (.retained ⟨0, Nat.zero_lt_succ j⟩ b)).hom) ≫
          ι (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  rw [Category.assoc, arithmeticFirstResidualAtlas_right, ← changedArithmeticAtlasIso_chart]
  have hi : ι (.initial b) = c (.initial b) ≫ (G).hom := by
    have h := changedArithmeticAtlasIso_chart hπ data H 1 j hj u hu (.initial b)
    change c (.initial b) ≫ (G).hom = (𝟙 _ ≫ 𝟙 _) ≫ κ (.initial b) at h
    rw [Category.id_comp, Category.id_comp] at h
    change 𝟙 _ ≫ κ (.initial b) = c (.initial b) ≫ (G).hom
    rw [Category.id_comp]
    exact h.symm
  rw [hi, ← Category.assoc, arithmeticLabeledAtlas_initial_edge_overlap,
    Category.assoc, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
