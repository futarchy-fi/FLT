/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothHorizontalCyclicParameter
public import FLT.Mazur.WeierstrassSmoothCoefficientCartesian

/-!
# The horizontal residue smooth point is the original coefficient smooth point

The independent named smooth parameter gives the actual smooth point on the
residue cubic. Both integral product specializations project to that point,
retaining the cyclic inverse-tangent orientation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ} (D : SplitNodeDepth W π depth)
  (d : WeierstrassDividedDepth.Data W π k) (hk0 : 0 < k) (hk : 2 * k < depth) (hπ : π ≠ 0)
local notation "K" => ResidueField R
local notation "C" => SmoothHorizontalResidueRing D
local notation "L" => K[T;T⁻¹]
local notation "P" => SmoothYParameterRing D
local notation "V" => W.map (algebraMap R K)
local notation "p" => smoothHorizontalPoint W (π ^ k)
local notation "r" => smoothHorizontalResidueParameter D
local notation "e₁" => smoothHorizontalFirstResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6
local notation "e₂" => smoothHorizontalSecondResidue D k hk0 hk hπ
  d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6

omit d hk0 hk hπ in
/-- The actual smooth residue point on the independent parameter factor. -/
def smoothHorizontalResiduePoint (hd : 0 < depth) :
    Spec (.of C) ⟶ (integralSmoothOpen V).toScheme :=
  Spec.map (CommRingCat.ofHom (r).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap L P)) ≫ (infinityResidueSmoothIso D hd).hom

omit d hk0 hk hπ in
/-- The actual residue smooth point lies over its independent product coefficient map. -/
@[reassoc] theorem smoothHorizontalResiduePoint_structure (hd : 0 < depth) :
    smoothHorizontalResiduePoint D hd ≫ integralSmoothStructure V =
      Spec.map (CommRingCat.ofHom (algebraMap K C)) := by
  have h : (infinityResidueSmoothIso D hd).hom ≫ integralSmoothStructure V =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    rw [← infinityResidueSmoothGroupIso_inv]
    exact (infinityResidueSmoothGroupIso D hd).inv.hom.hom.hom.w
  simp only [smoothHorizontalResiduePoint, Category.assoc, h]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro t
  change r (algebraMap L P (algebraMap K L t)) = algebraMap K C t
  rw [← IsScalarTower.algebraMap_apply, AlgHom.commutes]

/-- The first integral smooth input is the projection of the actual residue smooth point. -/
theorem smoothHorizontalFirstResiduePoint_original :
    Spec.map (CommRingCat.ofHom (e₁).toRingHom) ≫ p =
      smoothHorizontalResiduePoint D (by omega) ≫ originalSmoothCoefficientMap K W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have hp : p ≫ (integralSmoothOpen W).ι =
      Spec.map (CommRingCat.ofHom (smoothHorizontalY W (π ^ k)).toRingHom) ≫
        integralCurveChart W 1 :=
    (smoothHorizontalLeft_inclusion W (π ^ k)).symm.trans
      (smoothHorizontal_common W (π ^ k))
  simp only [Category.assoc, hp, smoothHorizontalResiduePoint,
    originalSmoothCoefficientMap_inclusion, infinityResidueSmoothIso_contraction,
    infinityResidueContraction]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro t
  exact smoothHorizontalFirstResidue_y D d hk0 hk hπ t

/-- The second integral smooth input is the projection of the actual residue smooth point. -/
theorem smoothHorizontalSecondResiduePoint_original :
    Spec.map (CommRingCat.ofHom (e₂).toRingHom) ≫ p =
      smoothHorizontalResiduePoint D (by omega) ≫ originalSmoothCoefficientMap K W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have hp : p ≫ (integralSmoothOpen W).ι =
      Spec.map (CommRingCat.ofHom (smoothHorizontalY W (π ^ k)).toRingHom) ≫
        integralCurveChart W 1 :=
    (smoothHorizontalLeft_inclusion W (π ^ k)).symm.trans
      (smoothHorizontal_common W (π ^ k))
  simp only [Category.assoc, hp, smoothHorizontalResiduePoint,
    originalSmoothCoefficientMap_inclusion, infinityResidueSmoothIso_contraction,
    infinityResidueContraction]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro t
  exact smoothHorizontalSecondResidue_y D d hk0 hk hπ t

omit d hk0 hk hπ in
/-- The cyclic inverse tangent is precisely this coefficient smooth point. -/
theorem smoothHorizontalResiduePoint_cyclic {start : ℕ} (s : ℕ)
    (hs : 2 * (start + s + 1) ≤ depth) :
    Spec.map (CommRingCat.ofHom
        (smoothHorizontalLaurentEvaluation D (smoothHorizontalTangentUnit D)⁻¹).toRingHom) ≫
      (positiveEqualityCyclicSmoothGroupIso D s hs).hom.hom.hom.hom.left =
        smoothHorizontalResiduePoint D (by omega) :=
  smoothHorizontalCyclicParameter_original D s hs

end FLT.Mazur.WeierstrassIntegralChart
