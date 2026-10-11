/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstAtlasCoordinates
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
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (hn : 1 ≤ n)

local notation "v" => finiteNormalizedChart hπ data 0 hn

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le hn))
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + 0))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "q" => previousOriginalMap hπ d e
local notation "U" => firstDividedAffineCover hπ data hn

local notation "D" => firstDividedInputCover hπ data hn
local notation "I" => WeierstrassSuccessiveX.modificationCenter W (π ^ (start + 0)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
variable (a : ((firstDividedInputCover hπ data hn).X none).affineCover.I₀)

/-- The original infinity coordinates on the actual simultaneous affine branch. -/
def firstDividedInfinityHom : Coordinate W 1 →+* (U).X ⟨none, a⟩ :=
  affineChartRingHom (firstDividedInputProjection hπ data hn ⟨none, a⟩)

/-- The infinity ring presentation is exactly the constructed input projection. -/
@[simp] theorem firstDividedInfinityHom_spec :
    Spec.map (CommRingCat.ofHom (firstDividedInfinityHom hπ data hn a)) =
      firstDividedInputProjection hπ data hn ⟨none, a⟩ := affineChartRingHom_spec _

/-- The crossed branch retains the actual original Y-chart input. -/
@[reassoc] theorem firstDividedInfinityHom_original :
    Spec.map (CommRingCat.ofHom (firstDividedInfinityHom hπ data hn a)) ≫
        integralCurveChart W 1 = firstDividedOriginalInput hπ data hn ⟨none, a⟩ := by
  rw [firstDividedInfinityHom_spec]
  have h := firstDividedInputProjection_original hπ data hn ⟨none, a⟩
  change firstDividedInputProjection hπ data hn ⟨none, a⟩ ≫
    finiteInfinityChart hπ data 1 hn ≫ finiteGlobalContraction hπ data 1 hn = _ at h
  rwa [finiteInfinityChart_contraction] at h

/-- The entire successive output center on each infinity-input affine member is a unit. -/
theorem firstDividedInfinity_center :
    (I).map (firstDividedAlpha hπ data hn ⟨none, a⟩) = ⊤ := by
  have hp : firstDividedParameter hπ data hn ⟨none, a⟩ ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom (firstDividedInfinityHom hπ data hn a)) ≫
        integralCurveChart W 1) ≫ integralCurveStructure W := by
    rw [firstDividedInfinityHom_original]
    exact firstDividedParameter_structure hπ data hn ⟨none, a⟩
  apply WeierstrassSuccessiveX.successiveInfinityPresentation_center (S := (U).X ⟨none, a⟩)
    W (π ^ (start + 0)) π (e).b3 (e).b4 (e).b6
    (by rw [← factor3_step hπ d e]; exact (d).factor3)
    (by rw [← factor4_step hπ d e]; exact (d).factor4)
    (by rw [← factor6_step hπ d e]; exact (d).factor6)
    1 (Or.inr rfl) (firstDividedParameter hπ data hn ⟨none, a⟩)
    (firstDividedAlpha hπ data hn ⟨none, a⟩) (firstDividedInfinityHom hπ data hn a) hp
  simpa only [firstDividedInfinityHom_original, previousOriginalMap] using
    firstDividedAlpha_addition hπ data hn ⟨none, a⟩

end FLT.Mazur.WeierstrassDividedDepth
