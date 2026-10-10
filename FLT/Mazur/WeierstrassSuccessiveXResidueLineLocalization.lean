/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXResidueLineHorizontal

/-!
# The full algebra map of the punctured horizontal line

The geometric lift to the horizontal open is the spectrum of the localization
of the original line map. This retains all tensor functions and the inverse
horizontal parameter.
-/

@[expose] public noncomputable section
open IsLocalRing AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (r : ResidueField R) (hr : r * (r + residue R W.a₁) = 0)
local notation "K" => ResidueField R
local notation "A" => ScalarExtension W (π ^ k) π b3 b4 b6 K
local notation "u" => tensorCoord W (π ^ k) π b3 b4 b6 K 2
local notation "L" => residueSuccessiveLineMap D k hk0 hk b3 b4 b6 h3 h4 r hr

/-- The original Laurent restriction extends to the entire horizontal localization. -/
def residueLineHorizontalMap : Localization.Away u →ₐ[K] K[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom u (f := Polynomial.toLaurentAlg.comp L) (by
    change IsUnit (Polynomial.toLaurent (L u))
    rw [residueSuccessiveLineMap_coord]
    change IsUnit (Polynomial.toLaurent (Polynomial.X : Polynomial K))
    rw [Polynomial.toLaurent_X]
    exact LaurentPolynomial.isUnit_T 1)

/-- Every original tensor function restricts by the original line parameter. -/
@[simp] theorem residueLineHorizontalMap_base (z : A) :
    residueLineHorizontalMap D k hk0 hk b3 b4 b6 h3 h4 r hr
      (algebraMap A (Localization.Away u) z) = Polynomial.toLaurent (L z) := by
  rw [residueLineHorizontalMap, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The inverse horizontal function restricts to the inverse Laurent parameter. -/
theorem residueLineHorizontalMap_inverse :
    residueLineHorizontalMap D k hk0 hk b3 b4 b6 h3 h4 r hr
      (IsLocalization.Away.invSelf u) = LaurentPolynomial.T (-1) := by
  have h := congrArg (residueLineHorizontalMap D k hk0 hk b3 b4 b6 h3 h4 r hr)
    (IsLocalization.Away.mul_invSelf (S := Localization.Away u) u)
  rw [map_mul, map_one, residueLineHorizontalMap_base,
    residueSuccessiveLineMap_coord] at h
  change Polynomial.toLaurent (Polynomial.X : Polynomial K) * _ = 1 at h
  rw [Polynomial.toLaurent_X] at h
  apply (LaurentPolynomial.isUnit_T (R := K) 1).mul_left_cancel
  exact h.trans (by rw [← LaurentPolynomial.T_add]; rfl)

/-- The spectrum of the explicit localization map retains the full line inclusion. -/
@[reassoc] theorem residueLineHorizontalMap_spec_comp :
    Spec.map (CommRingCat.ofHom
      (residueLineHorizontalMap D k hk0 hk b3 b4 b6 h3 h4 r hr).toRingHom) ≫
        PrincipalOpenTensor.inclusion K (coord W (π ^ k) π b3 b4 b6 2) =
      ProjectiveLine.overlapLeft K ≫
        residueSuccessiveLineImmersion D k hk0 hk b3 b4 b6 h3 h4 r hr := by
  rw [residueSuccessiveLineImmersion_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact residueLineHorizontalMap_base D k hk0 hk b3 b4 b6 h3 h4 r hr z

/-- The geometric horizontal lift is exactly the explicit localized line map. -/
theorem residueLineToHorizontal_eq_spec :
    residueLineToHorizontal D k hk0 hk b3 b4 b6 h3 h4 r hr =
      Spec.map (CommRingCat.ofHom
        (residueLineHorizontalMap D k hk0 hk b3 b4 b6 h3 h4 r hr).toRingHom) := by
  apply (cancel_mono (PrincipalOpenTensor.inclusion K
    (coord W (π ^ k) π b3 b4 b6 2))).mp
  rw [residueLineToHorizontal_comp, residueLineHorizontalMap_spec_comp]

end FLT.Mazur.WeierstrassSuccessiveX
