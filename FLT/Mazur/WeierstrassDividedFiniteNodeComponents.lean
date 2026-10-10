/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SpecChartIdealPreimage
public import FLT.Mazur.WeierstrassDividedFiniteResidueNodes
public import FLT.Mazur.WeierstrassSuccessiveXResidueNodeIdeals

/-!
# Ordered component loci inside the finite residue model

The full tensor ideals define loci in the actual finite atlas. Their inverse
images under the two ordered node embeddings retain the conic and line branches.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 e)
local notation "T" => ScalarExtension W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "a" => finiteSuccessiveTensorChart hπ data K j hj
local notation "t" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 0
local notation "v" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 1
local notation "u" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K 2

/-- The first actual finite node retains the conic component as the u-zero branch. -/
theorem finiteResidueFirstNode_conicLocus :
    finiteResidueFirstNode hπ data D j hj hk0 hk ⁻¹'
      (a '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeU c} : Set (MiddleNodeOpen c)) := by
  rw [finiteResidueFirstNode, residueMiddleFirstNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus, residueFirstNodeMap_conicIdeal]

/-- The opposite actual finite node retains the same conic as its u-zero branch. -/
theorem finiteResidueSecondNode_conicLocus :
    finiteResidueSecondNode hπ data D j hj hk0 hk ⁻¹'
      (a '' PrimeSpectrum.zeroLocus (Ideal.span {u} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeU c} : Set (MiddleNodeOpen c)) := by
  rw [finiteResidueSecondNode, residueMiddleSecondNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus, residueSecondNodeMap_conicIdeal]

/-- The zero-slope tensor line retains its ordered attachment inside the finite atlas. -/
theorem finiteResidueFirstNode_lineLocus :
    finiteResidueFirstNode hπ data D j hj hk0 hk ⁻¹'
      (a '' PrimeSpectrum.zeroLocus (Ideal.span {t, v} : Set T)) =
        PrimeSpectrum.zeroLocus (Ideal.span {middleNodeZ c} : Set (MiddleNodeOpen c)) := by
  rw [finiteResidueFirstNode, residueMiddleFirstNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus, residueFirstNodeMap_lineIdeal]

/-- The opposite-slope tensor line retains the other ordered attachment in the finite atlas. -/
theorem finiteResidueSecondNode_lineLocus :
    finiteResidueSecondNode hπ data D j hj hk0 hk ⁻¹'
      (a '' PrimeSpectrum.zeroLocus
        (Ideal.span {t, v + algebraMap K T (residue R W.a₁)} : Set T)) =
          PrimeSpectrum.zeroLocus (Ideal.span {middleNodeZ c} : Set (MiddleNodeOpen c)) := by
  rw [finiteResidueSecondNode, residueMiddleSecondNodeChart_eq_spec,
    SpecChartIdeal.preimage_image_zeroLocus]
  exact congrArg (fun I : Ideal (MiddleNodeOpen c) =>
    PrimeSpectrum.zeroLocus (I : Set (MiddleNodeOpen c)))
    (residueSecondNodeMap_lineIdeal D (start + j) hk0 hk
      (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e))

end FLT.Mazur.WeierstrassDividedDepth
