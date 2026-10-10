/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroResidue
public import FLT.Mazur.WeierstrassSuccessiveXTensorContraction
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The full scale-one residue spectrum and its original contraction

The actual tensor spectrum is the entire horizontal fiber. Its preceding
contraction keeps the quadratic horizontal function and its product with v,
including the divided constant at middle depth.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "P" =>
  WeierstrassDilatation.Coordinate W (π ^ k) (π * b3) (π * b4) (π ^ 2 * b6)
local notation "t" => WeierstrassModificationX.fiberT a c
local notation "v" => WeierstrassModificationX.fiberV a c
local notation "q" => v * (v + algebraMap K F a) - algebraMap K F c * t ^ 2

/-- The complete horizontal model identifies the original tensor spectrum. -/
def zeroResidueFiberIso : Spec (.of F) ≅ Spec (.of T) :=
  Scheme.Spec.mapIso
    (zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).toRingEquiv.toCommRingCatIso.op

/-- The full original preceding contraction on the normalized horizontal fiber. -/
def zeroResiduePreviousMap : P →ₐ[R] F :=
  ((zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).toAlgHom.restrictScalars R).comp
    (tensorPreviousMap W (π ^ k) π b3 b4 b6 K)

/-- The original horizontal coordinate is the complete quadratic, retaining c. -/
theorem zeroResiduePreviousMap_x : zeroResiduePreviousMap D k hk0 hk b3 b4 b6 h3 h4
    (WeierstrassDilatation.x W (π ^ k) (π * b3) (π * b4) (π ^ 2 * b6)) = q := by
  change zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
    (tensorPreviousMap W (π ^ k) π b3 b4 b6 K _) = _
  rw [tensorPreviousMap_x, zeroResidueFiberEquiv_u]

/-- The original vertical coordinate is the quadratic times the original tangent slope. -/
theorem zeroResiduePreviousMap_y : zeroResiduePreviousMap D k hk0 hk b3 b4 b6 h3 h4
    (WeierstrassDilatation.y W (π ^ k) (π * b3) (π * b4) (π ^ 2 * b6)) = q * v := by
  change zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4
    (tensorPreviousMap W (π ^ k) π b3 b4 b6 K _) = _
  rw [tensorPreviousMap_y, map_mul, zeroResidueFiberEquiv_u, zeroResidueFiberEquiv_v]

/-- The spectrum comparison preserves the residue-field structure. -/
@[reassoc] theorem zeroResidueFiberIso_structure :
    (zeroResidueFiberIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap K T)) =
        Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext
    (zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4).commutes)

/-- Every original preceding-chart function agrees through the spectrum comparison. -/
@[reassoc] theorem zeroResidueFiberIso_previous :
    (zeroResidueFiberIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
      Spec.map (CommRingCat.ofHom (tensorPreviousMap W (π ^ k) π b3 b4 b6 K).toRingHom) =
        Spec.map (CommRingCat.ofHom
          (zeroResiduePreviousMap D k hk0 hk b3 b4 b6 h3 h4).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassSuccessiveX
