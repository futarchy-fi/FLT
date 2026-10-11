/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInteriorConicPunctures
public import FLT.Mazur.WeierstrassSmoothSuccessiveTensorOutput
public import FLT.Mazur.ProjectiveLineUniversalLaurentEvaluation
public import FLT.Mazur.WeierstrassDividedAdjacentParameterStructure

/-!
# Genuine successive outputs on the original labeled cyclic components

Both actual outputs lie in their original projective punctures after Laurent
multiplication. The cyclic group parameter is the inverse tangent character.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth) (j : Fin s)
local notation "𝕂" => ResidueField R
local notation "e" => data (Fin.mk (j.val + 1) (by omega))
local notation "C" => SmoothHorizontalResidueRing D
local notation "A" => ScalarExtension W (π ^ (start + j.val)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 𝕂
local notation "g" => olderGlobalTensorChart hπ data 𝕂 j.val (by omega)
  (s - j.val) (by omega)
local notation "transport" => eqToHom (finiteGlobalTensorModel_index_congr hπ data 𝕂
  (by omega : j.val + 1 + (s - j.val) ≤ n) hs (by omega))
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap 𝕂 C))
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R 𝕂)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "b" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (smoothHorizontalResidueConic D)))

local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D
local notation "q" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (ProjectiveLineUniversalAction.laurentPairEvaluation (K := 𝕂) τ⁻¹ z)))

/-- The actual first output retains its original cyclic puncture and character. -/
theorem interiorHorizontalFirstTensorOutput_cycle :
    Spec.map (CommRingCat.ofHom
        (smoothSuccessiveFirstTensorOutput (k := start + j.val) e hπ D
          (by omega)).toRingHom) ≫ g ≫ transport =
      Spec.map (CommRingCat.ofHom
        (smoothHorizontalLaurentEvaluation D (τ * z)).toRingHom) ≫
          ProjectiveLine.overlapLeft 𝕂 ≫ ProjectiveLine.right 𝕂 ≫
            (Z ⟨j.val + 2, by omega⟩).left := by
  rw [smoothSuccessiveFirstTensorOutput_conic (k := start + j.val) e hπ D (by omega) (by omega),
    lineSpec_comp, lineSpec_comp, ← residueSuccessiveConicImmersion_eq_spec]
  have h := congrArg (Spec.map (CommRingCat.ofHom
    (smoothHorizontalLaurentEvaluation D (τ * z)).toRingHom) ≫ ·)
      (interiorConicFirstPuncture_cycle hπ data D s hs hstart hk hp j)
  simpa only [olderGlobalMiddleConic, Category.assoc] using h

/-- Universal projective scaling gives the actual first output on its labeled component. -/
theorem interiorHorizontalFirstTensorOutput_universal :
    Spec.map (CommRingCat.ofHom
        (smoothSuccessiveFirstTensorOutput (k := start + j.val) e hπ D
          (by omega)).toRingHom) ≫ g ≫ transport =
      q ≫ ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
        ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] true ≫
          ProjectiveLineUniversalAction.action 𝕂 ≫ (Z ⟨j.val + 2, by omega⟩).left := by
  rw [interiorHorizontalFirstTensorOutput_cycle hπ data D s hs hstart hk hp j]
  have h := congrArg (· ≫ (Z ⟨j.val + 2, by omega⟩).left)
    (ProjectiveLineUniversalAction.laurentPairEvaluation_right_action (K := 𝕂) τ⁻¹ z)
  simp only [inv_inv, Category.assoc] at h
  exact h.symm

/-- The actual second output retains its original cyclic puncture and character. -/
theorem interiorHorizontalSecondTensorOutput_cycle :
    Spec.map (CommRingCat.ofHom
        (smoothSuccessiveSecondTensorOutput (k := start + j.val) e hπ D
          (by omega)).toRingHom) ≫ g ≫ transport =
      Spec.map (CommRingCat.ofHom
        (smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)).toRingHom) ≫
          ProjectiveLine.overlapLeft 𝕂 ≫ ProjectiveLine.left 𝕂 ≫
            (Z ⟨2 * s + 2 - j.val, by omega⟩).left := by
  rw [smoothSuccessiveSecondTensorOutput_conic (k := start + j.val) e hπ D (by omega) (by omega),
    lineSpec_comp, lineSpec_comp, ← residueSuccessiveConicImmersion_eq_spec]
  have h := congrArg (Spec.map (CommRingCat.ofHom
    (smoothHorizontalLaurentEvaluation D (τ⁻¹ * z)).toRingHom) ≫ ·)
      (interiorConicSecondPuncture_cycle hπ data D s hs hstart hk hp j)
  simpa only [olderGlobalMiddleConic, Category.assoc] using h

/-- Universal projective scaling gives the actual second output on its labeled component. -/
theorem interiorHorizontalSecondTensorOutput_universal :
    Spec.map (CommRingCat.ofHom
        (smoothSuccessiveSecondTensorOutput (k := start + j.val) e hπ D
          (by omega)).toRingHom) ≫ g ≫ transport =
      q ≫ ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
        ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] false ≫
          ProjectiveLineUniversalAction.action 𝕂 ≫ (Z ⟨2 * s + 2 - j.val, by omega⟩).left := by
  rw [interiorHorizontalSecondTensorOutput_cycle hπ data D s hs hstart hk hp j]
  have h := congrArg (· ≫ (Z ⟨2 * s + 2 - j.val, by omega⟩).left)
    (ProjectiveLineUniversalAction.laurentPairEvaluation_action (K := 𝕂) τ⁻¹ z)
  simp only [Category.assoc] at h
  exact h.symm

end FLT.Mazur.WeierstrassDividedDepth
