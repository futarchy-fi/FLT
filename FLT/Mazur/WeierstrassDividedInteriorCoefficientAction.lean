/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInteriorHorizontalCyclicInput
public import FLT.Mazur.WeierstrassDividedCoefficientActionIndexTransport
public import FLT.Mazur.WeierstrassDividedSmoothSuccessiveCoefficientAction
public import FLT.Mazur.WeierstrassSmoothSuccessiveTensorOutput

/-!
# The actual relative coefficient action on interior independent inputs

Transport the proved original residue action to the final finite stage.
The resulting relative morphisms retain both original tensor inputs and outputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth) (j : Fin s)
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1) (by omega))
local notation "C" => SmoothHorizontalResidueRing D
local notation "A" => ScalarExtension W (π ^ (start + j.val)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "g" => olderGlobalTensorChart hπ data K j.val (by omega)
  (s - j.val) (by omega)
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data K
  (by omega : j.val + 1 + (s - j.val) ≤ n) hs (by omega))
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap K C))
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "V" => W.map (algebraMap R K)
local notation "a" => smoothHorizontalResiduePoint D (by omega)
local notation "B" => finiteGlobalCoefficientOverAction hπ data (s + 1) hs K

/-- The genuine first residue action is the actual relative action on the interior input. -/
theorem interiorHorizontalFirstTensorOutput_over :
    lift (Over.homMk (U := Over.mk c) («V» := (integralSmoothGroup V).X) a
      (smoothHorizontalResiduePoint_structure D (by omega)))
      (interiorHorizontalTensorOverPoint hπ data D s hs j
        (smoothSuccessiveFirstTensorInput (k := start + j.val) D e
          (by omega) (by omega))) ≫ B =
      interiorHorizontalTensorOverPoint hπ data D s hs j
        (smoothSuccessiveFirstTensorOutput (k := start + j.val) e hπ D (by omega)) := by
  rw [finiteGlobalCoefficientOverAction_points]
  apply Over.OverMorphism.ext
  have h := smoothSuccessiveFirstResidue_coefficientPointAction hπ data j.val
    (by omega) (s - j.val) (by omega) D (by omega)
  simp only [smoothSuccessiveFirstResidue_tensorPoint hπ data j.val
    (by omega) (s - j.val) (by omega) D (by omega) (by omega)] at h
  change (finiteGlobalCoefficientOverPointAction hπ data (s + 1) hs K _ _ _).left = _
  simp only [finiteGlobalCoefficientOverPointAction, Over.homMk_left,
    interiorHorizontalTensorOverPoint]
  simp only [← Category.assoc]
  rw [finiteGlobalCoefficientPointAction_index_transport hπ data K
    (by omega) hs (by omega)]
  · exact congrArg (· ≫ transport) h
  · rw [Category.assoc, olderGlobalTensorChart_structure,
      smoothHorizontalResiduePoint_structure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext (smoothSuccessiveFirstTensorInput
      (k := start + j.val) D e (by omega) (by omega)).commutes).symm

/-- The genuine second residue action is the actual relative action on the interior input. -/
theorem interiorHorizontalSecondTensorOutput_over :
    lift (Over.homMk (U := Over.mk c) («V» := (integralSmoothGroup V).X) a
      (smoothHorizontalResiduePoint_structure D (by omega)))
      (interiorHorizontalTensorOverPoint hπ data D s hs j
        (smoothSuccessiveSecondTensorInput (k := start + j.val) D e
          (by omega) (by omega))) ≫ B =
      interiorHorizontalTensorOverPoint hπ data D s hs j
        (smoothSuccessiveSecondTensorOutput (k := start + j.val) e hπ D (by omega)) := by
  rw [finiteGlobalCoefficientOverAction_points]
  apply Over.OverMorphism.ext
  have h := smoothSuccessiveSecondResidue_coefficientPointAction hπ data j.val
    (by omega) (s - j.val) (by omega) D (by omega)
  simp only [smoothSuccessiveSecondResidue_tensorPoint hπ data j.val
    (by omega) (s - j.val) (by omega) D (by omega) (by omega)] at h
  change (finiteGlobalCoefficientOverPointAction hπ data (s + 1) hs K _ _ _).left = _
  simp only [finiteGlobalCoefficientOverPointAction, Over.homMk_left,
    interiorHorizontalTensorOverPoint]
  simp only [← Category.assoc]
  rw [finiteGlobalCoefficientPointAction_index_transport hπ data K
    (by omega) hs (by omega)]
  · exact congrArg (· ≫ transport) h
  · rw [Category.assoc, olderGlobalTensorChart_structure,
      smoothHorizontalResiduePoint_structure, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact (RingHom.ext (smoothSuccessiveSecondTensorInput
      (k := start + j.val) D e (by omega) (by omega)).commutes).symm

end FLT.Mazur.WeierstrassDividedDepth
