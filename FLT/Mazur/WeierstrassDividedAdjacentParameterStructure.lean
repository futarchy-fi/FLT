/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedAdjacentParameterOrigins
public import FLT.Mazur.WeierstrassDividedTerminalParameterStructure

/-!
# Adjacent full parameters preserve the original residue-field structure

The structure square follows the actual tensor charts through stage transport.
Both complete conic parameters and both complete horizontal lines are over the field.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))

/-- Stage-index transport preserves the actual coefficient projection. -/
@[reassoc] theorem finiteGlobalTensorModel_structure_transport
    (S : Type u) [CommRing S] [Algebra R S] {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b) :
    eqToHom (finiteGlobalTensorModel_index_congr hπ data S ha hb he) ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (finiteGlobalStructure hπ data b hb) =
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (finiteGlobalStructure hπ data a ha) := by
  subst b
  simp only [eqToHom_refl, Category.id_comp]

variable [IsLocalRing R] (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 2 + r) hr)

/-- The reassociated old tensor chart preserves all original residue coefficients. -/
@[reassoc] theorem adjacentRetainedOldGlobalTensorChart_structure :
    adjacentRetainedOldGlobalTensorChart hπ data K j hj r hr ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap K
        (ScalarExtension W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) K))) := by
  rw [adjacentRetainedOldGlobalTensorChart_transport, Category.assoc,
    finiteGlobalTensorModel_structure_transport hπ data K _ _ (by omega),
    olderGlobalTensorChart_structure]

variable {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hk : 2 * (start + j + 1) ≤ depth)
local notation "c" => residue R (Data.b6 d)
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap K (ConicParameterOpen c)))

/-- The complete first positive-depth parameter keeps its coefficient structure. -/
@[reassoc] theorem adjacentRetainedFirstParameter_structure (hk0 : 0 < start + j) :
    adjacentRetainedFirstParameter hπ data D j hj hk0 hk r hr ≫ p = b := by
  rw [adjacentRetainedFirstParameter]
  simp only [Category.assoc, adjacentRetainedOldGlobalTensorChart_structure]
  rw [residueSuccessiveConicImmersion_eq_spec]
  rw [terminalComponent_algebra_structure
    (residueSuccessiveConicMap D (start + j) hk0 hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d))]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicFirstOpen a c))]
  exact terminalComponent_algebra_structure (conicFirstParameterEquiv a c ha).symm.toAlgHom

/-- The complete second positive-depth parameter keeps its coefficient structure. -/
@[reassoc] theorem adjacentRetainedSecondParameter_structure (hk0 : 0 < start + j) :
    adjacentRetainedSecondParameter hπ data D j hj hk0 hk r hr ≫ p = b := by
  rw [adjacentRetainedSecondParameter]
  simp only [Category.assoc, adjacentRetainedOldGlobalTensorChart_structure]
  rw [residueSuccessiveConicImmersion_eq_spec]
  rw [terminalComponent_algebra_structure
    (residueSuccessiveConicMap D (start + j) hk0 hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d))]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicSecondOpen a c))]
  exact terminalComponent_algebra_structure (conicSecondParameterEquiv a c ha).symm.toAlgHom

/-- The complete first scale-one parameter keeps its coefficient structure. -/
@[reassoc] theorem adjacentZeroFirstParameter_structure (hk0 : start + j = 0) :
    adjacentZeroFirstParameter hπ data D j hj hk0 hk r hr ≫ p = b := by
  rw [adjacentZeroFirstParameter]
  simp only [Category.assoc, adjacentRetainedOldGlobalTensorChart_structure]
  rw [zeroResidueConicImmersion]
  rw [Category.assoc, zeroResidueFiberIso_structure]
  change _ ≫ Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [terminalComponent_algebra_structure (fiberConicMap a c)]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicFirstOpen a c))]
  exact terminalComponent_algebra_structure (conicFirstParameterEquiv a c ha).symm.toAlgHom

/-- The complete second scale-one parameter keeps its coefficient structure. -/
@[reassoc] theorem adjacentZeroSecondParameter_structure (hk0 : start + j = 0) :
    adjacentZeroSecondParameter hπ data D j hj hk0 hk r hr ≫ p = b := by
  rw [adjacentZeroSecondParameter]
  simp only [Category.assoc, adjacentRetainedOldGlobalTensorChart_structure]
  rw [zeroResidueConicImmersion]
  rw [Category.assoc, zeroResidueFiberIso_structure]
  change _ ≫ Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [terminalComponent_algebra_structure (fiberConicMap a c)]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicSecondOpen a c))]
  exact terminalComponent_algebra_structure (conicSecondParameterEquiv a c ha).symm.toAlgHom

variable (rOld : ℕ) (hrOld : j + 1 + rOld ≤ n) (hk0 : 0 < start + j)
local notation "pOld" => pullback.fst q (finiteGlobalStructure hπ data (j + 1 + rOld) hrOld)

/-- The original first full horizontal line is over the residue field. -/
@[reassoc] theorem olderGlobalMiddleFirstLine_structure :
    olderGlobalMiddleFirstLine hπ data D j hj rOld hrOld hk0 hk ≫ pOld =
      ProjectiveLine.chartToBase K := by
  rw [olderGlobalMiddleFirstLine, Category.assoc, olderGlobalTensorChart_structure,
    residueSuccessiveLineImmersion_eq_spec]
  exact terminalComponent_algebra_structure
    (residueSuccessiveLineMap D (start + j) hk0 hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
      0 (middle_first_root (W.map (residue R))))

/-- The original second full horizontal line is over the residue field. -/
@[reassoc] theorem olderGlobalMiddleSecondLine_structure :
    olderGlobalMiddleSecondLine hπ data D j hj rOld hrOld hk0 hk ≫ pOld =
      ProjectiveLine.chartToBase K := by
  rw [olderGlobalMiddleSecondLine, Category.assoc, olderGlobalTensorChart_structure,
    residueSuccessiveLineImmersion_eq_spec]
  exact terminalComponent_algebra_structure
    (residueSuccessiveLineMap D (start + j) hk0 hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
      (-a) (middle_second_root (W.map (residue R))))

end FLT.Mazur.WeierstrassDividedDepth
