/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingBaseChange
public import FLT.Mazur.PolygonSmoothingBranchSwap
public import FLT.Mazur.PrincipalOpenTensor

/-!
# Base change of the original punctured smoothing branches

Both actual coordinate localizations commute with arbitrary coefficient
extension. The comparison preserves restriction of every original function,
and its spectrum identifies the actual pullback of each punctured chart.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.PolygonSmoothing

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- Normalize the actual tensor principal open of the first branch. -/
def leftTensorPunctureEquiv (t : R) :
    Localization.Away ((1 : S) ⊗ₜ[R] leftCoordinate t) ≃ₐ[S]
      LeftPuncture (algebraMap R S t) :=
  IsLocalization.algEquivOfAlgEquiv _ _ (baseChangeEquiv R S t)
    (M := Submonoid.powers ((1 : S) ⊗ₜ[R] leftCoordinate t))
    (T := Submonoid.powers (leftCoordinate (algebraMap R S t))) (by
      rw [Submonoid.map_powers, baseChangeEquiv_left])

/-- Normalize the actual tensor principal open of the second branch. -/
def rightTensorPunctureEquiv (t : R) :
    Localization.Away ((1 : S) ⊗ₜ[R] rightCoordinate t) ≃ₐ[S]
      RightPuncture (algebraMap R S t) :=
  IsLocalization.algEquivOfAlgEquiv _ _ (baseChangeEquiv R S t)
    (M := Submonoid.powers ((1 : S) ⊗ₜ[R] rightCoordinate t))
    (T := Submonoid.powers (rightCoordinate (algebraMap R S t))) (by
      rw [Submonoid.map_powers, baseChangeEquiv_right])

/-- The full first branch localization commutes with extension of coefficients. -/
def leftPunctureBaseChangeEquiv (t : R) :
    S ⊗[R] LeftPuncture t ≃ₐ[S] LeftPuncture (algebraMap R S t) :=
  (PrincipalOpenTensor.equiv S (leftCoordinate t)).trans (leftTensorPunctureEquiv R S t)

/-- The full second branch localization commutes with extension of coefficients. -/
def rightPunctureBaseChangeEquiv (t : R) :
    S ⊗[R] RightPuncture t ≃ₐ[S] RightPuncture (algebraMap R S t) :=
  (PrincipalOpenTensor.equiv S (rightCoordinate t)).trans (rightTensorPunctureEquiv R S t)

/-- Every original chart function retains its first-branch restriction under base change. -/
theorem leftPunctureBaseChangeEquiv_restrict (t : R) (s : S) (z : ChartRing t) :
    leftPunctureBaseChangeEquiv R S t (s ⊗ₜ[R] algebraMap (ChartRing t) _ z) =
      algebraMap (ChartRing (algebraMap R S t)) _ (baseChangeEquiv R S t (s ⊗ₜ[R] z)) := by
  rw [leftPunctureBaseChangeEquiv, AlgEquiv.trans_apply, PrincipalOpenTensor.equiv_tmul_base]
  exact IsLocalization.algEquivOfAlgEquiv_eq _ _

/-- Every original chart function retains its second-branch restriction under base change. -/
theorem rightPunctureBaseChangeEquiv_restrict (t : R) (s : S) (z : ChartRing t) :
    rightPunctureBaseChangeEquiv R S t (s ⊗ₜ[R] algebraMap (ChartRing t) _ z) =
      algebraMap (ChartRing (algebraMap R S t)) _ (baseChangeEquiv R S t (s ⊗ₜ[R] z)) := by
  rw [rightPunctureBaseChangeEquiv, AlgEquiv.trans_apply, PrincipalOpenTensor.equiv_tmul_base]
  exact IsLocalization.algEquivOfAlgEquiv_eq _ _

attribute [local irreducible] leftPunctureBaseChangeEquiv rightPunctureBaseChangeEquiv

/-- The first punctured chart after coefficient extension is its actual scheme pullback. -/
def leftPunctureBaseChangeIso (t : R) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (LeftPuncture t)))) ≅
        Spec (.of (LeftPuncture (algebraMap R S t))) :=
  pullbackSpecIso R S (LeftPuncture t) ≪≫
    Scheme.Spec.mapIso (leftPunctureBaseChangeEquiv R S t).symm.toRingEquiv.toCommRingCatIso.op

/-- The second punctured chart after coefficient extension is its actual scheme pullback. -/
def rightPunctureBaseChangeIso (t : R) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (RightPuncture t)))) ≅
        Spec (.of (RightPuncture (algebraMap R S t))) :=
  pullbackSpecIso R S (RightPuncture t) ≪≫
    Scheme.Spec.mapIso (rightPunctureBaseChangeEquiv R S t).symm.toRingEquiv.toCommRingCatIso.op

/-- The first puncture's comparison retains the actual coefficient projection. -/
@[reassoc] theorem leftPunctureBaseChangeIso_inv_fst (t : R) :
    (leftPunctureBaseChangeIso R S t).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (LeftPuncture (algebraMap R S t)))) := by
  change Spec.map (CommRingCat.ofHom (leftPunctureBaseChangeEquiv R S t).toRingHom) ≫
    (pullbackSpecIso R S (LeftPuncture t)).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (leftPunctureBaseChangeEquiv R S t).toAlgHom.comp_algebraMap

/-- The second puncture's comparison retains the actual coefficient projection. -/
@[reassoc] theorem rightPunctureBaseChangeIso_inv_fst (t : R) :
    (rightPunctureBaseChangeIso R S t).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (RightPuncture (algebraMap R S t)))) := by
  change Spec.map (CommRingCat.ofHom (rightPunctureBaseChangeEquiv R S t).toRingHom) ≫
    (pullbackSpecIso R S (RightPuncture t)).inv ≫ pullback.fst _ _ = _
  rw [pullbackSpecIso_inv_fst', ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (rightPunctureBaseChangeEquiv R S t).toAlgHom.comp_algebraMap

/-- Coefficient extension on the entire original left puncture. -/
def leftPunctureCoefficientMap (t : R) :
    LeftPuncture t →+* LeftPuncture (algebraMap R S t) :=
  (leftPunctureBaseChangeEquiv R S t).toRingHom.comp
    (Algebra.TensorProduct.includeRight : LeftPuncture t →ₐ[R] S ⊗[R] LeftPuncture t).toRingHom

/-- The left puncture's second projection is its actual coefficient-extension map. -/
@[reassoc] theorem leftPunctureBaseChangeIso_inv_snd (t : R) :
    (leftPunctureBaseChangeIso R S t).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (leftPunctureCoefficientMap R S t)) := by
  change Spec.map (CommRingCat.ofHom (leftPunctureBaseChangeEquiv R S t).toRingHom) ≫
    (pullbackSpecIso R S (LeftPuncture t)).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

/-- Coefficient extension on the entire original right puncture. -/
def rightPunctureCoefficientMap (t : R) :
    RightPuncture t →+* RightPuncture (algebraMap R S t) :=
  (rightPunctureBaseChangeEquiv R S t).toRingHom.comp
    (Algebra.TensorProduct.includeRight : RightPuncture t →ₐ[R] S ⊗[R] RightPuncture t).toRingHom

/-- The right puncture's second projection is its actual coefficient-extension map. -/
@[reassoc] theorem rightPunctureBaseChangeIso_inv_snd (t : R) :
    (rightPunctureBaseChangeIso R S t).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (rightPunctureCoefficientMap R S t)) := by
  change Spec.map (CommRingCat.ofHom (rightPunctureBaseChangeEquiv R S t).toRingHom) ≫
    (pullbackSpecIso R S (RightPuncture t)).inv ≫ pullback.snd _ _ = _
  rw [pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

end FLT.Mazur.PolygonSmoothing
