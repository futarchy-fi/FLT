/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstAtlasCoordinates
public import FLT.Mazur.WeierstrassDividedGlobalStepExterior
public import FLT.Mazur.WeierstrassSuccessiveExteriorCenter

/-!
# Actual retained-exterior coordinates on the divided-output atlas

The crossed branch keeps the original x-direction coordinates and their
flat input projection. Its horizontal coordinate therefore remains regular.
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
local notation "X" => WeierstrassModificationX.Coordinate W (π ^ (start + 0))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "c" => WeierstrassModificationX.fromOriginal W (π ^ (start + 0))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d)
variable (a : ((firstDividedInputCover hπ data hn).X (some none)).affineCover.I₀)

/-- The actual retained exterior's coordinate presentation on the simultaneous atlas. -/
def firstDividedExteriorHom : X →+* (U).X ⟨some none, a⟩ :=
  affineChartRingHom (firstDividedInputProjection hπ data hn ⟨some none, a⟩)

/-- The exterior coordinate presentation is exactly its constructed projection. -/
@[simp] theorem firstDividedExteriorHom_spec :
    Spec.map (CommRingCat.ofHom (firstDividedExteriorHom hπ data hn a)) =
      firstDividedInputProjection hπ data hn ⟨some none, a⟩ := affineChartRingHom_spec _

/-- Flatness is supplied by the actual simultaneous input projection. -/
theorem firstDividedExteriorHom_flat : RingHom.Flat (firstDividedExteriorHom hπ data hn a) := by
  apply (Flat.SpecMap_iff (f := CommRingCat.ofHom
    (firstDividedExteriorHom hπ data hn a))).mp
  rw [firstDividedExteriorHom_spec]
  exact firstDividedInputProjection_flat hπ data hn ⟨some none, a⟩

/-- The retained horizontal coordinate is regular on every actual crossed affine member. -/
theorem firstDividedExteriorHom_horizontal_regular :
    IsRegular (firstDividedExteriorHom hπ data hn a
      (WeierstrassModificationX.x W (π ^ (start + 0)) (d).b3 (d).b4 (d).b6)) :=
  flatRingHom_isRegular _ (firstDividedExteriorHom_flat hπ data hn a)
    (WeierstrassModificationX.x_regular W _ _ _ _ (pow_ne_zero _ hπ))

/-- The retained input coordinates contract to the original point used by the genuine action. -/
@[reassoc] theorem firstDividedExteriorHom_original :
    Spec.map (CommRingCat.ofHom ((firstDividedExteriorHom hπ data hn a).comp
        (c).toRingHom)) ≫ integralCurveChart W 2 =
      firstDividedOriginalInput hπ data hn ⟨some none, a⟩ := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, firstDividedExteriorHom_spec]
  have h := firstDividedInputProjection_original hπ data hn ⟨some none, a⟩
  change firstDividedInputProjection hπ data hn ⟨some none, a⟩ ≫
    finiteSuccessiveRetainedChart hπ data 0 hn ≫ finiteGlobalContraction hπ data 1 hn = _ at h
  rwa [firstRetainedChart_contraction] at h

/-- The input and output ring presentations retain the identical coefficient map. -/
theorem firstDividedExterior_coefficients :
    (firstDividedAlpha hπ data hn ⟨some none, a⟩).comp (algebraMap R B) =
      (firstDividedExteriorHom hπ data hn a).comp (algebraMap R X) := by
  have he := congrArg (fun t => t ≫ integralCurveStructure W)
    (firstDividedAlpha_addition hπ data hn ⟨some none, a⟩)
  rw [leftSmoothPointAddition_structure, firstDividedParameter_structure,
    ← firstDividedExteriorHom_original hπ data hn a] at he
  simp only [Category.assoc, integralCurveChart_structure] at he
  have out (γ : B →+* (U).X ⟨some none, a⟩) :
      Spec.map (CommRingCat.ofHom (γ.comp (q).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 2))) =
      Spec.map (CommRingCat.ofHom (γ.comp (algebraMap R B))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact congrArg γ ((q).commutes r)
  have inp (γ : X →+* (U).X ⟨some none, a⟩) :
      Spec.map (CommRingCat.ofHom (γ.comp (c).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 2))) =
      Spec.map (CommRingCat.ofHom (γ.comp (algebraMap R X))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact congrArg γ ((c).commutes r)
  rw [chartStructure, out, inp] at he
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective he)

end FLT.Mazur.WeierstrassDividedDepth
