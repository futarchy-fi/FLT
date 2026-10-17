/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedAdjacentParameters

/-!
# Full normalized adjacent equations in the actual arithmetic target

Cancel the common invertible full edge parameter after transporting both
original endpoints. This identifies the geometric base of incoming residuals.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "t" => parameter R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "N" => arithmeticRetainedFixedSmoothingIso data H m (j + 1) hj
local notation "O" => twistedRetainedOrientation data H m
local notation "κ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu

/-- Both normalized consecutive charts agree along the entire original geometric edge. -/
@[reassoc] theorem changedArithmeticAtlas_normalized_adjacent
    (a : ℕ) (ha : a + 1 < j + 1) (b : Bool) :
    leftBranchOpen Q τ ≫ (O b).hom ≫ κ (.retained ⟨a, by omega⟩ b) =
      precedingBranch Q τ ≫ (O b).hom ≫ κ (.retained ⟨a + 1, ha⟩ b) := by
  have h := congrArg (fun f ↦ f ≫ (G).hom)
    (arithmeticLabeledAtlas_adjacent_overlap hπ data H m (j + 1) hj a ha b)
  simp only [Category.assoc, changedArithmeticAtlasIso_chart,
    changedArithmeticAtlasIso, twistedArithmeticAtlasIso, changedArithmeticAtlasToTwisted,
    Iso.trans_hom, Iso.symm_hom, Iso.refl_inv] at h
  apply (cancel_epi
    (arithmeticRetainedAdjacentParameter data H m (j + 1) hj ⟨a, by omega⟩).hom).mp
  simpa only [Category.assoc, changedArithmeticAtlasObject, twistedArithmeticAtlasObject,
    Category.id_comp, arithmeticRetainedAdjacentParameter_outgoing_assoc,
    arithmeticRetainedAdjacentParameter_incoming_assoc hπ] using h

end FLT.Mazur.WeierstrassDividedDepth
