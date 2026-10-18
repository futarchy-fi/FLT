/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlas
public import FLT.Mazur.WeierstrassSuccessiveArithmeticTensorRestrictionSquare
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# Original coefficient projections on retained and terminal arithmetic nodes

The indexed retained tensor charts retain the projection of their full
original charts, including arbitrary depth and both branch orientations.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction

/-- Both original successive tensor branches preserve their quotient coefficients. -/
@[reassoc] theorem originalArithmeticTensorBranch_base {R : Type} [CommRing R]
    (π : R) (m : ℕ) (W : WeierstrassCurve R) (s b3 b4 b6 : R)
    (ha : IsUnit W.a₁) (hs : π ∣ s) (h2 : π ∣ W.a₂)
    (h3 : π ∣ b3) (h4 : π ∣ b4) (h6 : π ∣ b6) (b : Bool) :
    arithmeticTensorBranchChart π m W s b3 b4 b6 ha hs h2 h3 h4 h6 b ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (Quotient R π m) (ScalarExtension W s π b3 b4 b6 (Quotient R π m)))) =
      chartStructure (Quotient R π m) (parameter R π m) := by
  rw [arithmeticTensorBranchChart, Category.assoc, arithmeticSuccessiveTensorIso_structure]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact arithmeticNodeChart_structure ..
  · exact arithmeticOppositeNodeChart_structure ..

variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m

/-- Indexing a retained tensor chart does not change its coefficient projection. -/
@[reassoc] theorem arithmeticRetainedTensorChart_base (a : ℕ) (ha : a < k) :
    arithmeticRetainedTensorChart hπ data m k hk a ha ≫
      finiteGlobalArithmeticStructure hπ data k hk m =
        Spec.map (CommRingCat.ofHom (algebraMap Q
          (ScalarExtension W (π ^ (start + a)) π
            (data ⟨a + 1, by omega⟩).b3 (data ⟨a + 1, by omega⟩).b4
            (data ⟨a + 1, by omega⟩).b6 Q))) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show a + 1 ≤ k by omega)
  rw [arithmeticRetainedTensorChart_eq hπ data m (a + 1 + r) hk a ha r hk]
  exact finiteArithmeticOlderTensorChart_structure hπ data m a (by omega) r hk

/-- Every original full retained node is over its actual arithmetic quotient. -/
@[reassoc] theorem arithmeticLabeledRetainedChart_base (a : Fin k) (b : Bool) :
    arithmeticLabeledRetainedChart hπ data H m k hk a b ≫
      finiteGlobalArithmeticStructure hπ data k hk m =
        chartStructure Q (parameter R π m) := by
  rw [arithmeticLabeledRetainedChart, Category.assoc, arithmeticRetainedTensorChart_base]
  exact originalArithmeticTensorBranch_base ..

local notation "d" => data (Fin.mk k (Nat.lt_succ_of_le hk))
local notation "c" => WeierstrassDilatation.arithmeticTerminalSmoothing π m W
  (π ^ (start + k)) (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit (H.scale k)
  H.a2_div (H.b4_div _) (H.b6_div _)

/-- The entire original terminal normalization preserves its coefficient projection. -/
@[reassoc] theorem arithmeticLabeledTerminalChart_base :
    arithmeticLabeledTerminalChart hπ data H m k hk ≫
      finiteGlobalArithmeticStructure hπ data k hk m =
        Spec.map (CommRingCat.ofHom (algebraMap Q (NodalFiber.Coordinate c))) := by
  rw [arithmeticLabeledTerminalChart, Category.assoc, finiteArithmeticDividedTensorChart_structure]
  exact WeierstrassDilatation.arithmeticTerminalNodeIso_structure ..

end FLT.Mazur.WeierstrassDividedDepth
