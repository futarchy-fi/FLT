/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedFixedRightBoundary
public import FLT.Mazur.WeierstrassDividedSecondPrecedingAdjacent
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledInitialEdge

/-!
# The original initial edge with its full normalized right parameter

The first retained chart has an actual initial neighbor. Its full Laurent
parameter is retained before applying the predecessor's opposite correction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "t" => parameter R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "q" => arithmeticStartOneQuotient W H.a1_unit π m
local notation "V" => arithmeticRetainedFullCorrection data H m (j + 1) hj
local notation "N" => arithmeticRetainedFixedSmoothingIso data H m (j + 1) hj
local notation "O" => twistedRetainedOrientation data H m

/-- The full right parameter of any normalized retained chart, including depth zero. -/
def arithmeticRetainedRightParameter (a : Fin (j + 1)) : branchTorus Q ⟶ branchTorus Q :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := Q)
    (retainedFixedRightUnit t
      (retainedScaledCorrectionUnit t (retainedDepthScale q 1 a.val) (V a)))).toRingHom)

omit [IsDomain R] in
/-- The actual right boundary factors with this exact parameter. -/
@[reassoc] theorem arithmeticRetainedRightParameter_right (a : Fin (j + 1)) :
    rightBranchOpen Q t ≫ (N a).hom =
      arithmeticRetainedRightParameter data H m j hj a ≫ rightBranchOpen Q τ :=
  retainedFixedSmoothingChart_right ..

variable [IsBezout R]
local notation "κ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "I" => changedArithmeticAtlasIso hπ data H m j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu
local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ 1) H.a1_unit H.scale_div
local notation "E" => arithmeticInitialPunctureIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- The unchanged initial chart still has the original full global comparison. -/
@[reassoc] theorem changedArithmeticAtlas_initial_chart (b : Bool) :
    κ (.initial b) = c (.initial b) ≫ (G).hom := by
  have h := changedArithmeticAtlasIso_chart hπ data H m j hj u hu (.initial b)
  change c (.initial b) ≫ (G).hom = (𝟙 _ ≫ 𝟙 _) ≫ κ (.initial b) at h
  simpa only [Category.id_comp] using h.symm

/-- The original initial D(p) edge with the complete normalized retained right parameter. -/
@[reassoc] theorem changedArithmeticAtlas_normalized_initial (b : Bool) :
    P ≫ κ (.initial b) = (E).inv ≫
      arithmeticRetainedRightParameter data H m j hj ⟨0, Nat.zero_lt_succ j⟩ ≫
        rightBranchOpen Q τ ≫ (O b).hom ≫ κ (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  rw [changedArithmeticAtlas_initial_chart, ← Category.assoc,
    arithmeticLabeledAtlas_initial_edge_overlap hπ data H m (j + 1) hj
      (Nat.zero_lt_succ j) b, Category.assoc, Category.assoc,
    changedArithmeticAtlasIso_chart]
  have hi : (I (.retained ⟨0, Nat.zero_lt_succ j⟩ b)).hom =
      (N ⟨0, Nat.zero_lt_succ j⟩).hom ≫ (O b).hom := by
    simp only [changedArithmeticAtlasIso, twistedArithmeticAtlasIso,
      changedArithmeticAtlasToTwisted, Iso.trans_hom, Iso.symm_hom, Iso.refl_inv]
    exact Category.comp_id _
  rw [hi]
  simpa only [Category.assoc] using congrArg
    (fun f ↦ (E).inv ≫ f ≫ (O b).hom ≫ κ (.retained ⟨0, Nat.zero_lt_succ j⟩ b))
    (arithmeticRetainedRightParameter_right data H m j hj ⟨0, Nat.zero_lt_succ j⟩)

end FLT.Mazur.WeierstrassDividedDepth
