/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearInitialBoundaryGeometry
public import FLT.Mazur.WeierstrassCoefficientShearInitialConicProjection
public import FLT.Mazur.WeierstrassCoefficientShearRetainedReconstruction
public import FLT.Mazur.WeierstrassDividedInitialTensorBoundary
public import FLT.Mazur.WeierstrassCoefficientShearConicParameters
public import FLT.Mazur.WeierstrassConicZeroAffineParameter
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
/-!
# Arbitrary-root initial reciprocal overlaps in the complete coefficient gluing

The original tensor boundary equality attaches both full initial affine
parameters to their first retained lines, preserving each reciprocal sign.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (h1 : 1 ≤ n) (m : ℕ) (hm : 1 + m ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
variable (hs : algebraMap R S (π ^ start) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (g3 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (g4 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (g6 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "conic" => coefficientShearInitialConic hπ data S r (1 + m) hm hs g3 g4 hr
local notation "E" => conicZeroAffineIso c g6
local notation "F₁" => (E).hom ≫ coefficientConicFirstParameter (U).a₁ c hu conic
local notation "F₂" => (E).hom ≫ coefficientConicSecondParameter (U).a₁ c hu conic
local notation "line" => coefficientShearRetainedLine hπ data S r (1 + m) hm
  (Fin.mk 0 (by omega : 0 < 1 + m)) hs hp h3 h4 hr
local notation "L₁" => line 0 (middle_first_root U)
local notation "L₂" => line (-(U).a₁) (middle_second_root U)
local notation "G" => coefficientShearGluedIso hπ data S r (1 + m) hm

/-- The full first arbitrary-root parameter meets its retained line by signed reciprocal. -/
theorem coefficientShearRootInitialFirst_overlap :
    ProjectiveLine.overlapLeft S ≫ F₁ =
      Spec.map (CommRingCat.ofHom
        (PolygonScaledReciprocal.reciprocal a⁻¹).toRingHom) ≫
          ProjectiveLine.overlapLeft S ≫ L₁ := by
  rw [coefficientConicFirstParameter, ← Category.assoc, conicZeroAffineIso_puncture]
  have H := conicPuncturedFirst_spec c g6 U hu
  rw [← Category.assoc] at H
  rw [← Category.assoc, ← Category.assoc, ← H]
  apply (cancel_mono (G).hom).mp
  simp only [Category.assoc]
  rw [coefficientShearInitialConic_tensor_reconstruction]
  erw [coefficientShearInitialFirstLine_boundary_spec_assoc
    hπ d e S r hs hp h3 h4 hr g3 g4 g6 a ha]
  erw [initialRetainedGlobalTensor_boundary hπ data S h1 m hm]
  simp only [Fin.val_mk, Nat.add_zero]
  erw [Iso.hom_inv_id_assoc]
  erw [tensorShearLineToHorizontal_comp_assoc W (π ^ start) π (Data.b3 e) (Data.b4 e) (Data.b6 e)
    S r hs hp h3 h4 hr 0 (middle_first_root U)]
  erw [← coefficientShearRetainedTensorChart_line, Category.assoc,
    coefficientShearRetainedTensorChart_original hπ data S r 0 h1 m hm]
  rfl

/-- The full second arbitrary-root parameter meets its retained line by signed reciprocal. -/
theorem coefficientShearRootInitialSecond_overlap :
    ProjectiveLine.overlapLeft S ≫ F₂ =
      Spec.map (CommRingCat.ofHom
        (PolygonScaledReciprocal.reciprocal (-a)⁻¹).toRingHom) ≫
          ProjectiveLine.overlapLeft S ≫ L₂ := by
  rw [coefficientConicSecondParameter, ← Category.assoc, conicZeroAffineIso_puncture]
  have H := conicPuncturedSecond_spec c g6 U hu
  rw [← Category.assoc] at H
  rw [← Category.assoc, ← Category.assoc, ← H]
  apply (cancel_mono (G).hom).mp
  simp only [Category.assoc]
  rw [coefficientShearInitialConic_tensor_reconstruction]
  erw [coefficientShearInitialSecondLine_boundary_spec_assoc
    hπ d e S r hs hp h3 h4 hr g3 g4 g6 a ha]
  erw [initialRetainedGlobalTensor_boundary hπ data S h1 m hm]
  simp only [Fin.val_mk, Nat.add_zero]
  erw [Iso.hom_inv_id_assoc]
  erw [tensorShearLineToHorizontal_comp_assoc W (π ^ start) π (Data.b3 e) (Data.b4 e) (Data.b6 e)
    S r hs hp h3 h4 hr (-(U).a₁) (middle_second_root U)]
  erw [← coefficientShearRetainedTensorChart_line, Category.assoc,
    coefficientShearRetainedTensorChart_original hπ data S r 0 h1 m hm]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
