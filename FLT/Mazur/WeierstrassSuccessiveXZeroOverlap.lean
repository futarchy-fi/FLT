/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXZeroContraction
public import FLT.Mazur.WeierstrassSuccessiveXTensorOverlapGeometry
public import FLT.Mazur.PrincipalOpenTransportGeometry

/-!
# The complete first horizontal overlap

Normalizing the incidence principal open retains every original localized
function and the entire integral transition to the adjacent divided chart.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Limits
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
local notation "t" => WeierstrassModificationX.fiberT a c
local notation "F" => WeierstrassModificationX.FiberCoordinate a c
local notation "O" => Localization.Away t
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "t₀" => tensorCoord W (π ^ k) π b3 b4 b6 K 0
local notation "E" => zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4

/-- The full actual incidence localization survives the scale-one normalization. -/
def zeroResidueXOpenEquiv : TensorXOpen W (π ^ k) π b3 b4 b6 K ≃ₐ[K] O :=
  PrincipalOpenTransport.equiv E t₀ t (zeroResidueFiberEquiv_t D k hk0 hk b3 b4 b6 h3 h4)

/-- Every tensor function keeps its restriction under the full overlap comparison. -/
theorem zeroResidueXOpenEquiv_base (z : T) :
    zeroResidueXOpenEquiv D k hk0 hk b3 b4 b6 h3 h4 (algebraMap T _ z) =
      algebraMap F O (E z) := PrincipalOpenTransport.equiv_base _ _ _ _ z

/-- The full incidence open as an isomorphism of the original tensor principal spectrum. -/
def zeroResidueXOpenIso : Spec (.of O) ≅
    Spec (.of (TensorXOpen W (π ^ k) π b3 b4 b6 K)) :=
  Scheme.Spec.mapIso
    (zeroResidueXOpenEquiv D k hk0 hk b3 b4 b6 h3 h4).toRingEquiv.toCommRingCatIso.op

/-- The spectrum comparison commutes with the full original incidence-open inclusion. -/
@[reassoc] theorem zeroResidueXOpenIso_inclusion :
    (zeroResidueXOpenIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
      PrincipalOpenTransport.inclusion t₀ =
        PrincipalOpenTransport.inclusion t ≫
          (zeroResidueFiberIso D k hk0 hk b3 b4 b6 h3 h4).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (zeroResidueXOpenEquiv_base D k hk0 hk b3 b4 b6 h3 h4)

/-- The normalization square is cartesian, so the full original open is retained. -/
theorem zeroResidueXOpenIso_isPullback :
    IsPullback (zeroResidueXOpenIso D k hk0 hk b3 b4 b6 h3 h4).hom
      (PrincipalOpenTransport.inclusion t) (PrincipalOpenTransport.inclusion t₀)
      (zeroResidueFiberIso D k hk0 hk b3 b4 b6 h3 h4).hom :=
  IsPullback.of_horiz_isIso ⟨zeroResidueXOpenIso_inclusion D k hk0 hk b3 b4 b6 h3 h4⟩

/-- The full original adjacent divided principal open, with no component removed. -/
def zeroResidueAdjacentIso : Spec (.of O) ≅
    Spec (.of (TensorDividedOpen W (π ^ k) π b3 b4 b6 K)) :=
  (zeroResidueXOpenIso D k hk0 hk b3 b4 b6 h3 h4).trans
    (tensorOverlapIso W (π ^ k) π b3 b4 b6 K)

/-- Every original integral overlap function agrees through the normalized transition. -/
@[reassoc] theorem zeroResidueAdjacentIso_original :
    (zeroResidueAdjacentIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
      tensorDividedOpenProjection W (π ^ k) π b3 b4 b6 K =
        (zeroResidueXOpenIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
          tensorXOpenProjection W (π ^ k) π b3 b4 b6 K ≫
            (overlapIso W (π ^ k) π b3 b4 b6).hom := by
  rw [zeroResidueAdjacentIso, Iso.trans_hom, Category.assoc, tensorOverlapIso_square]

end FLT.Mazur.WeierstrassSuccessiveX
