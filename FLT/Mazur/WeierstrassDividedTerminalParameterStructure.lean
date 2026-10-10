/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassConicZeroAffineParameter
public import FLT.Mazur.WeierstrassDividedTerminalBranchIntersection
public import FLT.Mazur.WeierstrassDividedTerminalZeroBranchIntersection
public import FLT.Mazur.WeierstrassDividedFinalNodeFamily
public import FLT.Mazur.WeierstrassSuccessiveXResidueComponentPoints

/-!
# Original coefficient structures of the full terminal conic parameters

The complete affine parameters, including the scale-one case, are morphisms
over the residue field. The argument uses their original algebra maps.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- A map of coefficient algebras preserves the spectrum structure morphism. -/
@[reassoc] theorem terminalComponent_algebra_structure {K A B : Type u}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (f : A →ₐ[K] B) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext f.commutes)

variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)
local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (j + 1) hj)
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap K (ConicParameterOpen c)))

/-- The complete first positive-depth parameter keeps its coefficient structure. -/
@[reassoc] theorem terminalConicFirstParameter_structure (hk0 : 0 < start + j) :
    terminalConicFirstParameter hπ data D j hj hk0 hk ≫ p = b := by
  rw [terminalConicFirstParameter]
  simp only [Category.assoc, globalSuccessiveTensorChart_structure]
  rw [residueSuccessiveConicImmersion_eq_spec]
  rw [terminalComponent_algebra_structure
    (residueSuccessiveConicMap D (start + j) hk0 hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d))]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicFirstOpen a c))]
  exact terminalComponent_algebra_structure (conicFirstParameterEquiv a c ha).symm.toAlgHom

/-- The complete second positive-depth parameter keeps its coefficient structure. -/
@[reassoc] theorem terminalConicSecondParameter_structure (hk0 : 0 < start + j) :
    terminalConicSecondParameter hπ data D j hj hk0 hk ≫ p = b := by
  rw [terminalConicSecondParameter]
  simp only [Category.assoc, globalSuccessiveTensorChart_structure]
  rw [residueSuccessiveConicImmersion_eq_spec]
  rw [terminalComponent_algebra_structure
    (residueSuccessiveConicMap D (start + j) hk0 hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d))]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicSecondOpen a c))]
  exact terminalComponent_algebra_structure (conicSecondParameterEquiv a c ha).symm.toAlgHom

/-- The complete first scale-one parameter keeps its coefficient structure. -/
@[reassoc] theorem terminalZeroConicFirstParameter_structure (hk0 : start + j = 0) :
    terminalZeroConicFirstParameter hπ data D j hj hk0 hk ≫ p = b := by
  rw [terminalZeroConicFirstParameter]
  simp only [Category.assoc, globalSuccessiveTensorChart_structure]
  rw [zeroResidueConicImmersion]
  rw [Category.assoc, zeroResidueFiberIso_structure]
  change _ ≫ Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [terminalComponent_algebra_structure (fiberConicMap a c)]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicFirstOpen a c))]
  exact terminalComponent_algebra_structure (conicFirstParameterEquiv a c ha).symm.toAlgHom

/-- The complete second scale-one parameter keeps its coefficient structure. -/
@[reassoc] theorem terminalZeroConicSecondParameter_structure (hk0 : start + j = 0) :
    terminalZeroConicSecondParameter hπ data D j hj hk0 hk ≫ p = b := by
  rw [terminalZeroConicSecondParameter]
  simp only [Category.assoc, globalSuccessiveTensorChart_structure]
  rw [zeroResidueConicImmersion]
  rw [Category.assoc, zeroResidueFiberIso_structure]
  change _ ≫ Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  rw [terminalComponent_algebra_structure (fiberConicMap a c)]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = _
  erw [terminalComponent_algebra_structure
    (Algebra.algHom K (ConicCoordinate a c) (ConicSecondOpen a c))]
  exact terminalComponent_algebra_structure (conicSecondParameterEquiv a c ha).symm.toAlgHom

end FLT.Mazur.WeierstrassDividedDepth
