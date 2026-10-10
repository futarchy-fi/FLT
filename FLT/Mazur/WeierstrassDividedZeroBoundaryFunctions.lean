/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSuccessiveOriginalY
public import FLT.Mazur.WeierstrassSuccessiveXZeroContraction
public import FLT.Mazur.WeierstrassModificationXFiberConic
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The complete first horizontal and infinity boundary functions

At depth zero the original horizontal function is the full conic factor,
and the original cubic y function is that factor times the original slope.
The localization comparisons retain every original restricted function.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth k : ℕ}
  (D : SplitNodeDepth W π depth) (e : Data W π (k + 1))
  (hk0 : k = 0) (hk : 2 * (k + 1) ≤ depth)
open WeierstrassSuccessiveX WeierstrassModificationX
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R e.b6
local notation "F" => FiberCoordinate a c
local notation "T" => ScalarExtension W (π ^ k) π e.b3 e.b4 e.b6 K
local notation "E" => zeroResidueFiberEquiv D k hk0 hk e.b3 e.b4 e.b6 e.factor3 e.factor4
local notation "u" => coord W (π ^ k) π e.b3 e.b4 e.b6 2
local notation "v" => coord W (π ^ k) π e.b3 e.b4 e.b6 1
local notation "q" => fiberConicFactor a c
local notation "w" => fiberV a c

/-- The original tensor y function with its named scalar-extension algebra retained. -/
def zeroBoundaryTensorY : T := (1 : K) ⊗ₜ[R] successiveOriginalY e
local notation "y₀" => zeroBoundaryTensorY e
local notation "u₀" => tensorCoord W (π ^ k) π e.b3 e.b4 e.b6 K 2

/-- The full first horizontal boundary is the original conic factor. -/
theorem zeroBoundary_horizontal : E ((1 : K) ⊗ₜ[R] u) = q :=
  zeroResidueFiberEquiv_u D k hk0 hk e.b3 e.b4 e.b6 e.factor3 e.factor4

/-- The original cubic y retains the full conic factor and tangent slope. -/
theorem zeroBoundary_originalY : E y₀ = q * w := by
  change E ((1 : K) ⊗ₜ[R] successiveOriginalY e) = q * w
  have hy : successiveOriginalY e = u * v := by
    unfold successiveOriginalY
    have hs : π ^ k = 1 := by rw [hk0, pow_zero]
    have hm : algebraMap R (Coordinate W (π ^ k) π e.b3 e.b4 e.b6) (π ^ k) = 1 := by
      rw [hs, map_one]
    rw [hm, one_mul]
  rw [hy]
  have hm : (1 : K) ⊗ₜ[R] (u * v) =
      ((1 : K) ⊗ₜ[R] u : T) * ((1 : K) ⊗ₜ[R] v : T) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hm, map_mul, zeroBoundary_horizontal]
  rw [show E ((1 : K) ⊗ₜ[R] v) = w from
    zeroResidueFiberEquiv_v D k hk0 hk e.b3 e.b4 e.b6 e.factor3 e.factor4]

/-- The entire original horizontal localization in normalized fiber coordinates. -/
def zeroHorizontalBoundaryEquiv :
    Localization.Away u₀ ≃ₐ[K] Localization.Away q :=
  PrincipalOpenTransport.equiv E _ q (zeroBoundary_horizontal D e hk0 hk)

/-- The entire original infinity localization in normalized fiber coordinates. -/
def zeroInfinityBoundaryEquiv :
    Localization.Away y₀ ≃ₐ[K]
      Localization.Away (q * w) :=
  PrincipalOpenTransport.equiv E _ (q * w) (zeroBoundary_originalY D e hk0 hk)

/-- Horizontal normalization retains restriction of all original functions. -/
theorem zeroHorizontalBoundaryEquiv_base (z : T) :
    zeroHorizontalBoundaryEquiv D e hk0 hk
      (algebraMap T (Localization.Away u₀) z) =
      algebraMap F (Localization.Away q) (E z) :=
  PrincipalOpenTransport.equiv_base _ _ _ _ z

/-- Infinity normalization retains restriction of all original functions. -/
theorem zeroInfinityBoundaryEquiv_base (z : T) :
    zeroInfinityBoundaryEquiv D e hk0 hk
      (algebraMap T (Localization.Away y₀) z) =
      algebraMap F (Localization.Away (q * w)) (E z) :=
  PrincipalOpenTransport.equiv_base _ _ _ _ z

/-- The entire normalized horizontal boundary as the original principal spectrum. -/
def zeroHorizontalBoundaryIso : Spec (.of (Localization.Away (q))) ≅
    Spec (.of (Localization.Away u₀)) :=
  Scheme.Spec.mapIso
    (zeroHorizontalBoundaryEquiv D e hk0 hk).toRingEquiv.toCommRingCatIso.op

/-- The horizontal comparison preserves the original full restriction square. -/
@[reassoc] theorem zeroHorizontalBoundaryIso_inclusion :
    (zeroHorizontalBoundaryIso D e hk0 hk).hom ≫
      PrincipalOpenTransport.inclusion u₀ =
        PrincipalOpenTransport.inclusion (q) ≫
          (zeroResidueFiberIso D k hk0 hk e.b3 e.b4 e.b6 e.factor3 e.factor4).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (zeroHorizontalBoundaryEquiv_base D e hk0 hk))

/-- The entire normalized infinity boundary as the original principal spectrum. -/
def zeroInfinityBoundaryIso : Spec (.of (Localization.Away (q * w))) ≅
    Spec (.of (Localization.Away y₀)) :=
  Scheme.Spec.mapIso
    (zeroInfinityBoundaryEquiv D e hk0 hk).toRingEquiv.toCommRingCatIso.op

/-- The infinity comparison preserves the original full restriction square. -/
@[reassoc] theorem zeroInfinityBoundaryIso_inclusion :
    (zeroInfinityBoundaryIso D e hk0 hk).hom ≫
      PrincipalOpenTransport.inclusion y₀ =
        PrincipalOpenTransport.inclusion (q * w) ≫
          (zeroResidueFiberIso D k hk0 hk e.b3 e.b4 e.b6 e.factor3 e.factor4).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (zeroInfinityBoundaryEquiv_base D e hk0 hk))

end FLT.Mazur.WeierstrassDividedDepth
