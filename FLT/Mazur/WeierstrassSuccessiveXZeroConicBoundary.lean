/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFiberConicOpen
public import FLT.Mazur.WeierstrassSuccessiveXZeroOverlap
public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# The full conic boundary at preceding depth zero

The scale-one tensor normalization gives the original horizontal fiber.
Its full conic incidence open is exactly the original tensor transition open.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (k : ℕ) (hk0 : k = 0) (hk : 2 * (k + 1) ≤ depth) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "c" => residue R b6
local notation "T" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "C₀" => ConicCoordinate a c
local notation "B" => Localization.Away (conicT a c)
local notation "t" => coord W (π ^ k) π b3 b4 b6 0
local notation "E" => zeroResidueFiberIso D k hk0 hk b3 b4 b6 h3 h4
local notation "i" => PrincipalOpenTransport.inclusion (conicT a c)

/-- The original closed conic in the actual scale-one tensor chart. -/
def zeroResidueConicImmersion : Spec (.of C₀) ⟶ Spec (.of T) :=
  fiberConicImmersion a c ≫ (E).hom

instance zeroResidueConicImmersion_isClosedImmersion :
    IsClosedImmersion (zeroResidueConicImmersion D k hk0 hk b3 b4 b6 h3 h4) :=
  inferInstanceAs (IsClosedImmersion (_ ≫ _))

/-- Normalize the entire original tensor incidence open to the original conic open. -/
def zeroResidueConicOpenEquiv : TensorXOpen W (π ^ k) π b3 b4 b6 K ≃ₐ[K] B :=
  (zeroResidueXOpenEquiv D k hk0 hk b3 b4 b6 h3 h4).trans (fiberConicOpenEquiv a c)

/-- The normalization keeps the restriction of every actual tensor function. -/
theorem zeroResidueConicOpenEquiv_base (z : T) :
    zeroResidueConicOpenEquiv D k hk0 hk b3 b4 b6 h3 h4 (algebraMap T _ z) =
      algebraMap C₀ B (fiberConicMap a c
        (zeroResidueFiberEquiv D k hk0 hk b3 b4 b6 h3 h4 z)) := by
  change fiberOpenToConic a c
    (zeroResidueXOpenEquiv D k hk0 hk b3 b4 b6 h3 h4 (algebraMap T _ z)) = _
  rw [zeroResidueXOpenEquiv_base, fiberOpenToConic_base]

/-- The complete original conic boundary at depth zero. -/
def zeroResidueConicBoundaryIso : Spec (.of B) ≅
    Spec (.of (TensorXOpen W (π ^ k) π b3 b4 b6 K)) :=
  (fiberConicOpenIso a c).trans (zeroResidueXOpenIso D k hk0 hk b3 b4 b6 h3 h4)

/-- The full boundary retains the original conic inclusion and tensor coordinate. -/
@[reassoc] theorem zeroResidueConicBoundaryIso_inclusion :
    (zeroResidueConicBoundaryIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
      PrincipalOpenTensor.inclusion K t =
        i ≫ zeroResidueConicImmersion D k hk0 hk b3 b4 b6 h3 h4 := by
  change (fiberConicOpenIso a c).hom ≫
    (zeroResidueXOpenIso D k hk0 hk b3 b4 b6 h3 h4).hom ≫
      PrincipalOpenTransport.inclusion _ = _
  rw [zeroResidueXOpenIso_inclusion, fiberConicOpenIso_inclusion_assoc]
  rfl

/-- The full zero-stage conic square is cartesian. -/
theorem zeroResidueConicBoundary_isPullback :
    IsPullback (zeroResidueConicBoundaryIso D k hk0 hk b3 b4 b6 h3 h4).hom i
      (PrincipalOpenTensor.inclusion K t)
      (zeroResidueConicImmersion D k hk0 hk b3 b4 b6 h3 h4) :=
  IsPullback.of_horiz_isIso_mono
    ⟨zeroResidueConicBoundaryIso_inclusion D k hk0 hk b3 b4 b6 h3 h4⟩

end FLT.Mazur.WeierstrassSuccessiveX
