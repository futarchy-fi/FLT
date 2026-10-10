/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXZeroResidueGeometry
public import FLT.Mazur.PrincipalOpenNormalization

/-!
# Full boundary localizations of the start-zero tensor chart

The original incidence, horizontal and vertical functions are units on the
whole chart. Their complete principal opens, with all original restriction
maps, are preserved by the same slope normalization.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (hdepth : 0 < depth) (k : ℕ) (hk : k = 0) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "P" => SlopeOpen a
local notation "T" => ScalarExtension W (π ^ k) b3 b4 b6 K
local notation "e" => zeroResidueSlopeEquiv D hdepth k hk b3 b4 b6 h3 h4 h6
local notation "tx" => ((1 : K) ⊗ₜ[R] x W (π ^ k) b3 b4 b6 : T)
/-- A named original tensor Y function retains the sealed tensor algebra in localizations. -/
def zeroResidueTensorY : T := (1 : K) ⊗ₜ[R] y W (π ^ k) b3 b4 b6
local notation "ty" => zeroResidueTensorY (W := W) (π := π) k b3 b4 b6
local notation "tt" => ((1 : K) ⊗ₜ[R] t W (π ^ k) b3 b4 b6 : T)

include D hdepth hk h3 h4 h6

/-- The original incidence boundary is the entire start-zero tensor chart. -/
theorem zeroResidue_tensorT_isUnit : IsUnit tt := by
  apply (MulEquiv.isUnit_map e).mp
  rw [zeroResidueSlopeEquiv_t]
  exact (slope_units a).2.2

/-- The original horizontal boundary is the entire start-zero tensor chart. -/
theorem zeroResidue_tensorX_isUnit : IsUnit tx := by
  apply (MulEquiv.isUnit_map e).mp
  rw [zeroResidueSlopeEquiv_x]
  exact (slope_units a).1.mul (slope_units a).2.1

/-- The original Y-boundary is the entire start-zero tensor chart. -/
theorem zeroResidue_tensorY_isUnit : IsUnit ty := by
  apply (MulEquiv.isUnit_map e).mp
  rw [zeroResidueTensorY, zeroResidueSlopeEquiv_y]
  exact ((slope_units a).1.mul (slope_units a).2.1).mul (slope_units a).1

/-- The whole original vertical localization is retained in normalized coordinates. -/
def zeroResidueYBoundaryIso : Spec (.of (Localization.Away ((e) ty))) ≅
    Spec (.of (Localization.Away ty)) := PrincipalOpenNormalization.specIso e ty

/-- The normalized Y-boundary retains every original restriction and cubic function. -/
@[reassoc] theorem zeroResidueYBoundaryIso_contraction :
    (zeroResidueYBoundaryIso D hdepth k hk b3 b4 b6 h3 h4 h6).hom ≫
      PrincipalOpenTensor.inclusion K (y W (π ^ k) b3 b4 b6) ≫
        TensorOpenChart.projection ≫ toCurve W (π ^ k) b3 b4 b6 h3 h4 h6 =
      Spec.map (CommRingCat.ofHom (algebraMap P (Localization.Away ((e) ty)))) ≫
        zeroResidueSlopeContraction D hdepth k hk b3 b4 b6 h3 h4 h6 := by
  change (PrincipalOpenNormalization.specIso e ty).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap T (Localization.Away ty))) ≫ _ = _
  rw [PrincipalOpenNormalization.specIso_inclusion_assoc]
  exact congrArg (fun f => Spec.map
    (CommRingCat.ofHom (algebraMap P (Localization.Away ((e) ty)))) ≫ f)
      (zeroResidueSlopeIso_contraction D hdepth k hk b3 b4 b6 h3 h4 h6)

/-- Localizing at the original vertical function loses no element of the tensor chart. -/
def zeroResidueYLocalizationEquiv : T ≃ₐ[K] Localization.Away ty :=
  (IsLocalization.atUnit T (Localization.Away ty) ty
    (zeroResidue_tensorY_isUnit D hdepth k hk b3 b4 b6 h3 h4 h6)).restrictScalars K

/-- This full-boundary equivalence is the original localization map on every function. -/
theorem zeroResidueYLocalizationEquiv_apply (z : T) :
    zeroResidueYLocalizationEquiv D hdepth k hk b3 b4 b6 h3 h4 h6 z =
      algebraMap T (Localization.Away ty) z := by
  exact (IsLocalization.atUnit T (Localization.Away ty) ty
    (zeroResidue_tensorY_isUnit D hdepth k hk b3 b4 b6 h3 h4 h6)).commutes z

end FLT.Mazur.WeierstrassModificationX
