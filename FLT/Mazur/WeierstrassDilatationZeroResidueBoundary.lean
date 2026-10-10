/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationZeroResidueGeometry
public import FLT.Mazur.WeierstrassNodalResidueCharts
public import FLT.Mazur.WeierstrassIntegralCurvePushout

/-!
# The whole original Y-boundary of the zero-depth terminal chart

The nodal overlap includes in the actual divided tensor chart. Its complete
original contraction and coefficient map agree with the tensor Y-boundary.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth) (k : ℕ) (hk : k = 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
open WeierstrassIntegralChart
local notation "K" => ResidueField R
local notation "N" => splitNodalEquation (residueTangentUnit D)
local notation "e" => zeroResidueNodalIso D hdepth k hk b3 b4 b6 h3 h4 h6
local notation "b" => nodalResidueBoundaryIso D hdepth 2 1
local notation "T" => ScalarExtension W (π ^ k) b3 b4 b6 K

/-- The entire nodal Y-open includes in the original zero-depth tensor chart. -/
def zeroResidueBoundaryInclusion : overlapScheme N 2 1 ⟶ Spec (.of T) :=
  overlapInclusion N 2 1 ≫ (e).hom

instance zeroResidueBoundaryInclusion_isOpenImmersion :
    IsOpenImmersion (zeroResidueBoundaryInclusion D hdepth k hk b3 b4 b6 h3 h4 h6) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- All original affine functions have the same restrictions on the full nodal boundary. -/
@[reassoc] theorem zeroResidueBoundary_original :
    (b).hom ≫ TensorOpenChart.projection ≫ overlapInclusion W 2 1 =
      overlapInclusion N 2 1 ≫
        Spec.map (CommRingCat.ofHom (zeroResidueOriginalMap D hdepth).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply congrArg AlgHom.toRingHom
    (show ((nodalResidueBoundaryEquiv D hdepth 2 1).toAlgHom.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight.comp (overlapRestriction W 2 1)) =
        ((overlapRestriction N 2 1).restrictScalars R).comp
          (zeroResidueOriginalMap D hdepth) from ?_)
  apply WeierstrassIntegralChart.hom_ext
  intro i
  change nodalResidueBoundaryEquiv D hdepth 2 1
    ((1 : K) ⊗ₜ[R] overlapCoord W 2 1 i) =
      algebraMap _ _ (zeroResidueOriginalMap D hdepth (coord W 2 i))
  rw [zeroResidueOriginalMap_coord]
  exact nodalResidueBoundaryEquiv_coord D hdepth 2 1 i

/-- The full terminal Y-boundary has its original projective cubic contraction. -/
@[reassoc] theorem zeroResidueBoundaryInclusion_contraction :
    zeroResidueBoundaryInclusion D hdepth k hk b3 b4 b6 h3 h4 h6 ≫
      TensorOpenChart.projection ≫ toCurve W (π ^ k) b3 b4 b6 h3 h4 h6 =
        (b).hom ≫ TensorOpenChart.projection ≫
          overlapInclusion W 2 1 ≫ integralCurveChart W 2 := by
  rw [zeroResidueBoundaryInclusion, Category.assoc, zeroResidueNodalIso_contraction,
    zeroResidueBoundary_original_assoc]
  rfl

/-- The original Y/Z transition agrees with the terminal boundary on the whole cubic. -/
@[reassoc] theorem zeroResidueBoundaryInclusion_infinity :
    zeroResidueBoundaryInclusion D hdepth k hk b3 b4 b6 h3 h4 h6 ≫
      TensorOpenChart.projection ≫ toCurve W (π ^ k) b3 b4 b6 h3 h4 h6 =
        (b).hom ≫ TensorOpenChart.projection ≫ affineBoundaryToY W ≫
          integralCurveChart W 1 := by
  rw [zeroResidueBoundaryInclusion_contraction]
  exact congrArg (fun f => (b).hom ≫ TensorOpenChart.projection ≫ f)
    (yz_isPullback W).w.symm

/-- The complete terminal boundary retains its original residue coefficient structure. -/
@[reassoc] theorem zeroResidueBoundaryInclusion_structure :
    zeroResidueBoundaryInclusion D hdepth k hk b3 b4 b6 h3 h4 h6 ≫
      Spec.map (CommRingCat.ofHom (algebraMap K T)) =
        Spec.map (CommRingCat.ofHom (algebraMap K (Overlap N 2 1))) := by
  rw [zeroResidueBoundaryInclusion, Category.assoc, zeroResidueNodalIso_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

end FLT.Mazur.WeierstrassDilatation
