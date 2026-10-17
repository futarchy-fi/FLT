/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedInitialBoundary

/-!
# The original initial boundary of the second corrected predecessor

When the predecessor has depth zero, the full original D(p) edge attaches
to it with its original parameter and the exact new opposite substitution.
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
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticResidualLiftAtlasChart hπ data H m j hj u hu
local notation "χ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ 1) H.a1_unit H.scale_div
local notation "E" => arithmeticInitialPunctureIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "B" => arithmeticRetainedRightParameter data H m j hj (Fin.mk 0 (Nat.zero_lt_succ j))
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu

/-- Initial labels are unchanged by both installed rounds of full node corrections. -/
theorem arithmeticSecondJointAtlasChart_initial (b : Bool) :
    ι (.initial b) = χ (.initial b) := by
  change 𝟙 _ ≫ 𝟙 _ ≫ χ (.initial b) = χ (.initial b)
  rw [Category.id_comp, Category.id_comp]

variable (ha : 1 = j)
local notation "M" => arithmeticSecondJointPrecedingIdentification hπ data H m j hj u hu 0 ha

/-- The first predecessor's full residual is attached to its actual original initial chart. -/
@[reassoc] theorem arithmeticSecondJointAtlas_preceding_initial (b : Bool) :
    P ≫ ι (.initial b) = (E).inv ≫ B ≫
      (punctureSpecIso (arithmeticSecondPrecedingOpposite hπ data H m j hj u hu b)).hom ≫
        rightBranchOpen Q (s b) ≫ (M b).hom ≫
          ι (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  rw [arithmeticSecondJointAtlasChart_initial]
  have h := changedArithmeticAtlas_normalized_initial hπ data H m j hj u hu b
  rw [← arithmeticResidualLiftAtlasChart_before hπ data H m j hj u hu
    ⟨0, Nat.zero_lt_succ j⟩ (show 0 < j by omega) b] at h
  apply h.trans
  exact congrArg (fun f ↦ (E).inv ≫ B ≫ f)
    (arithmeticSecondJointPreceding_right hπ data H m j hj u hu 0 ha b)

omit m in
/-- At stage two the initial boundary retains only its original full parameter. -/
@[reassoc] theorem arithmeticSecondJointAtlas_preceding_initial_second (b : Bool) :
    arithmeticInitialPunctureInclusion π 2 W (π ^ 1) H.a1_unit H.scale_div ≫
        arithmeticSecondJointAtlasChart hπ data H 2 j hj u hu (.initial b) =
      (arithmeticInitialPunctureIso π 2 W (π ^ 1)
        (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
          (H.b3_div _) (H.b4_div _) (H.b6_div _)).inv ≫
        arithmeticRetainedRightParameter data H 2 j hj ⟨0, Nat.zero_lt_succ j⟩ ≫
          rightBranchOpen (Quotient R π 2)
            (arithmeticSecondPrecedingSmoothing hπ data H 2 j hj u hu b) ≫
              (arithmeticSecondJointPrecedingIdentification hπ data H 2 j hj u hu 0 ha b).hom ≫
                arithmeticSecondJointAtlasChart hπ data H 2 j hj u hu
                  (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  have h := arithmeticSecondJointAtlas_preceding_initial hπ data H 2 j hj u hu ha b
  rw [arithmeticSecondPrecedingOpposite_second, punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth
