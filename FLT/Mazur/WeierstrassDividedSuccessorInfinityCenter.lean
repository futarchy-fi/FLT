/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessorAtlasCoordinates
public import FLT.Mazur.WeierstrassSuccessiveInfinityCenter

/-!
# Unit output centers for the actual infinity-input branch

The complete simultaneous atlas retains its genuine original Y input.
Center invariance then makes its successive output ideal a unit ideal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
  (a : finiteGlobalActionProduct hπ data j (Nat.le_of_succ_le hj) ⟶
    finiteGlobalModel hπ data j (Nat.le_of_succ_le hj))

local notation "v" => finiteNormalizedChart hπ data j hj

local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => successorDividedAffineCover hπ data j hj a

local notation "D" => successorDividedInputCover hπ data j hj a
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
variable (t : ((successorDividedInputCover hπ data j hj a).X none).affineCover.I₀)

/-- The original infinity coordinates on the actual simultaneous affine branch. -/
def successorDividedInfinityHom : Coordinate W 1 →+* (U).X ⟨none, t⟩ :=
  affineChartRingHom (successorDividedInputProjection hπ data j hj a ⟨none, t⟩)

/-- The infinity ring presentation is exactly the constructed input projection. -/
@[simp] theorem successorDividedInfinityHom_spec :
    Spec.map (CommRingCat.ofHom (successorDividedInfinityHom hπ data j hj a t)) =
      successorDividedInputProjection hπ data j hj a ⟨none, t⟩ := affineChartRingHom_spec _

/-- The crossed branch retains the actual original Y-chart input. -/
@[reassoc] theorem successorDividedInfinityHom_original :
    Spec.map (CommRingCat.ofHom (successorDividedInfinityHom hπ data j hj a t)) ≫
        integralCurveChart W 1 = successorDividedOriginalInput hπ data j hj a ⟨none, t⟩ := by
  rw [successorDividedInfinityHom_spec]
  have h := successorDividedInputProjection_original hπ data j hj a ⟨none, t⟩
  change successorDividedInputProjection hπ data j hj a ⟨none, t⟩ ≫
    finiteInfinityChart hπ data (j + 1) hj ≫ finiteGlobalContraction hπ data (j + 1) hj = _ at h
  rwa [finiteInfinityChart_contraction] at h

variable (ha : a ≫ finiteGlobalContraction hπ data j (Nat.le_of_succ_le hj) =
  finiteGlobalActionInput hπ data j (Nat.le_of_succ_le hj) ≫ leftSmoothFactorAddition W)
include ha

/-- The entire successive output center on each infinity-input affine member is a unit. -/
theorem successorDividedInfinity_center :
    (I).map (successorDividedAlpha hπ data j hj a ⟨none, t⟩) = ⊤ := by
  have hp : successorDividedParameter hπ data j hj a ⟨none, t⟩ ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom (successorDividedInfinityHom hπ data j hj a t)) ≫
        integralCurveChart W 1) ≫ integralCurveStructure W := by
    rw [successorDividedInfinityHom_original]
    exact successorDividedParameter_structure hπ data j hj a ⟨none, t⟩
  apply WeierstrassSuccessiveX.successiveInfinityPresentation_center (S := (U).X ⟨none, t⟩)
    W (π ^ (start + j)) π (e).b3 (e).b4 (e).b6
    (by rw [← factor3_step hπ d e]; exact (d).factor3)
    (by rw [← factor4_step hπ d e]; exact (d).factor4)
    (by rw [← factor6_step hπ d e]; exact (d).factor6)
    1 (Or.inr rfl) (successorDividedParameter hπ data j hj a ⟨none, t⟩)
    (successorDividedAlpha hπ data j hj a ⟨none, t⟩)
    (successorDividedInfinityHom hπ data j hj a t) hp
  simpa only [successorDividedInfinityHom_original, previousOriginalMap] using
    successorDividedAlpha_addition hπ data j hj a ha ⟨none, t⟩

end FLT.Mazur.WeierstrassDividedDepth
