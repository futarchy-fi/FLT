/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXModificationMap
public import FLT.Mazur.WeierstrassSuccessiveXLocalization

/-!
# The actual incidence-open comparison with the product-scale modification

Inverting the same original incidence function identifies the successive
chart with the original modification chart at the product scale. Both maps
retain every original function, not just their closed residue points.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "A" => Coordinate W s π b3 b4 b6
local notation "B" => WeierstrassModificationX.Coordinate W (s * π) b3 b4 b6
local notation "t" => coord W s π b3 b4 b6 0
local notation "t'" => WeierstrassModificationX.t W (s * π) b3 b4 b6
local notation "L" => XOpen W s π b3 b4 b6

/-- The original modification chart with its incidence function inverted. -/
abbrev ModificationIncidenceOpen := Localization.Away t'
local notation "M" => ModificationIncidenceOpen W s π b3 b4 b6

/-- The original localized incidence function as a unit. -/
def modificationIncidenceUnit : Mˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := M) t').unit

/-- The unit retains the original incidence function. -/
theorem modificationIncidenceUnit_val :
    (↑(modificationIncidenceUnit W s π b3 b4 b6) : M) = algebraMap B M t' :=
  IsUnit.unit_spec _

/-- The original modification functions on the successive incidence open. -/
def modificationIncidenceForward : M →ₐ[R] L :=
  IsLocalization.Away.liftAlgHom t'
    (f := (IsScalarTower.toAlgHom R A L).comp (modificationMap W s π b3 b4 b6)) (by
      change IsUnit (algebraMap A L (modificationMap W s π b3 b4 b6 t'))
      rw [modificationMap_t]
      exact IsLocalization.Away.algebraMap_isUnit _)

/-- The inverse substitution extends across the original incidence localization. -/
def modificationIncidenceBackward : L →ₐ[R] M :=
  IsLocalization.Away.liftAlgHom t
    (f := modificationIncidenceInverse W s π b3 b4 b6 (IsScalarTower.toAlgHom R B M)
      (modificationIncidenceUnit W s π b3 b4 b6)
      (modificationIncidenceUnit_val W s π b3 b4 b6).symm) (by
        rw [modificationIncidenceInverse_coord]
        exact IsLocalization.Away.algebraMap_isUnit _)

/-- The forward localization retains every original modification function. -/
@[simp] theorem modificationIncidenceForward_base (q : B) :
    modificationIncidenceForward W s π b3 b4 b6 (algebraMap B M q) =
      algebraMap A L (modificationMap W s π b3 b4 b6 q) := by
  rw [modificationIncidenceForward, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The reverse localization retains the explicit inverse on every successive function. -/
@[simp] theorem modificationIncidenceBackward_base (q : A) :
    modificationIncidenceBackward W s π b3 b4 b6 (algebraMap A L q) =
      modificationIncidenceInverse W s π b3 b4 b6 (IsScalarTower.toAlgHom R B M)
        (modificationIncidenceUnit W s π b3 b4 b6)
        (modificationIncidenceUnit_val W s π b3 b4 b6).symm q := by
  rw [modificationIncidenceBackward, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

/-- The original inverse incidence is the inverse incidence of the successive chart. -/
@[simp] theorem modificationIncidenceForward_inverse :
    modificationIncidenceForward W s π b3 b4 b6
      (↑(modificationIncidenceUnit W s π b3 b4 b6)⁻¹) =
        (↑(xOpenUnit W s π b3 b4 b6)⁻¹ : L) := by
  apply map_inverse_unit _ _ (xOpenUnit W s π b3 b4 b6)⁻¹
  simp only [inv_inv, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [modificationIncidenceUnit_val, modificationIncidenceForward_base,
    modificationMap_t, xOpenUnit_val]

/-- These actual incidence opens are isomorphic over the original coefficient ring. -/
def modificationIncidenceEquiv : M ≃ₐ[R] L := by
  apply AlgEquiv.ofAlgHom (modificationIncidenceForward W s π b3 b4 b6)
    (modificationIncidenceBackward W s π b3 b4 b6)
  · apply IsLocalization.algHom_ext (Submonoid.powers t)
    apply hom_ext
    intro i
    fin_cases i
    · change modificationIncidenceForward W s π b3 b4 b6
        (modificationIncidenceBackward W s π b3 b4 b6 (algebraMap A L t)) = _
      rw [modificationIncidenceBackward_base, modificationIncidenceInverse_coord]
      change modificationIncidenceForward W s π b3 b4 b6
        (algebraMap B M t') = algebraMap A L t
      rw [modificationIncidenceForward_base, modificationMap_t]
    · change modificationIncidenceForward W s π b3 b4 b6
        (modificationIncidenceBackward W s π b3 b4 b6
          (algebraMap A L (coord W s π b3 b4 b6 1))) = _
      rw [modificationIncidenceBackward_base, modificationIncidenceInverse_coord]
      change modificationIncidenceForward W s π b3 b4 b6
        (algebraMap B M (WeierstrassModificationX.v W (s * π) b3 b4 b6)) =
          algebraMap A L (coord W s π b3 b4 b6 1)
      rw [modificationIncidenceForward_base, modificationMap_v]
    · change modificationIncidenceForward W s π b3 b4 b6
        (modificationIncidenceBackward W s π b3 b4 b6
          (algebraMap A L (coord W s π b3 b4 b6 2))) = _
      rw [modificationIncidenceBackward_base, modificationIncidenceInverse_coord]
      change modificationIncidenceForward W s π b3 b4 b6
        (algebraMap R M π * (↑(modificationIncidenceUnit W s π b3 b4 b6)⁻¹ : M)) = _
      rw [map_mul, AlgHom.commutes, modificationIncidenceForward_inverse]
      have h := congrArg (algebraMap A L) (incidence W s π b3 b4 b6)
      rw [map_mul, ← IsScalarTower.algebraMap_apply R A, ← xOpenUnit_val] at h
      rw [← h, mul_right_comm, Units.mul_inv, one_mul]
      rfl
  · apply IsLocalization.algHom_ext (Submonoid.powers t')
    apply AlgHom.ext
    intro q
    change modificationIncidenceBackward W s π b3 b4 b6
      (modificationIncidenceForward W s π b3 b4 b6 (algebraMap B M q)) = _
    rw [modificationIncidenceForward_base, modificationIncidenceBackward_base]
    exact AlgHom.congr_fun (modificationIncidenceInverse_comp W s π b3 b4 b6
      (IsScalarTower.toAlgHom R B M) (modificationIncidenceUnit W s π b3 b4 b6)
      (modificationIncidenceUnit_val W s π b3 b4 b6).symm) q

end FLT.Mazur.WeierstrassSuccessiveX
