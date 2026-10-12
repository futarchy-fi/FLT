/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveResidueLineShearComparison
public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections

/-!
# Both original ordered retained lines in the coefficient equation model

Reconstruction identifies the full root-zero sheared lines with the original
ordered lines in the tensor residue fiber, at every retained depth.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (m : ℕ) (hm : j + 1 + m ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
variable (hs : algebraMap R (ResidueField R) (π ^ (start + j)) = 0)
  (hp : algebraMap R (ResidueField R) π = 0)
  (h3 : algebraMap R (ResidueField R) (data ⟨j + 1, by omega⟩).b3 = 0)
  (h4 : algebraMap R (ResidueField R) (data ⟨j + 1, by omega⟩).b4 = 0)
  (hr : (0 : ResidueField R) ^ 2 + algebraMap R (ResidueField R) W.a₁ * 0 -
    algebraMap R (ResidueField R) W.a₂ = 0)
local notation "L" => coefficientShearRetainedLine hπ data K 0 (j + 1 + m) hm
  (Fin.mk j (by omega)) hs hp h3 h4 hr
local notation "E" => coefficientShearGluedIso hπ data K 0 (j + 1 + m) hm

/-- Reconstruction identifies any root-zero sheared line with its original residue immersion. -/
@[reassoc] theorem coefficientShearRetainedLine_original
    (v : ResidueField R) (hv : v * (v + residue R W.a₁) = 0)
    (hu : v * (v + (rootShearCurve (W.map (residue R)) 0).a₁) = 0) :
    L v hu ≫ (E).hom =
      residueSuccessiveLineImmersion D (start + j) hk0 hk
        (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) v hv ≫
          olderGlobalTensorChart hπ data K j hj m hm := by
  rw [← coefficientShearRetainedTensorChart_line, Category.assoc,
    coefficientShearRetainedTensorChart_original hπ data K 0 j hj m hm,
    residueSuccessiveLineImmersion_eq_shear D hk0 hk d hs hp h3 h4 hr v hv hu]

/-- The first full line has exactly the original first ordered parameter. -/
@[reassoc] theorem coefficientShearRetainedFirst_original :
    L 0 (middle_first_root U) ≫ (E).hom =
      olderGlobalMiddleFirstLine hπ data D j hj m hm hk0 hk :=
  coefficientShearRetainedLine_original hπ data D j hj m hm hk0 hk hs hp h3 h4 hr
    0 (middle_first_root V) (middle_first_root U)

/-- The opposite full line retains its original signed slope and affine origin. -/
@[reassoc] theorem coefficientShearRetainedSecond_original :
    L (-(U).a₁) (middle_second_root U) ≫ (E).hom =
      olderGlobalMiddleSecondLine hπ data D j hj m hm hk0 hk := by
  have hv : (-(U).a₁) * (-(U).a₁ + residue R W.a₁) = 0 := by
    rw [rootShearZero_tangent]
    exact middle_second_root V
  rw [coefficientShearRetainedLine_original hπ data D j hj m hm hk0 hk hs hp h3 h4 hr
    (-(U).a₁) hv (middle_second_root U)]
  simp only [rootShearZero_tangent, WeierstrassCurve.map, olderGlobalMiddleSecondLine]

end FLT.Mazur.WeierstrassDividedDepth
