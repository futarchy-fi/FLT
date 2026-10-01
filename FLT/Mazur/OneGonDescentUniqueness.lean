/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonAffineDescent
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Uniqueness of descent from the affine normalization

Over a field, the map to the pinched chart is an epimorphism of schemes.
Thus uniqueness of descent holds for arbitrary target schemes. This does
not construct existence of descent for nonaffine targets.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.PolygonNodePresentation
open FLT.Mazur.OneGonPinchingAlgebra

namespace FLT.Mazur.OneGonDescentUniqueness

universe u
variable {K : Type u} [Field K]

/-- Pullback on global functions is injective for the pinching map. -/
theorem appTop_injective :
    Function.Injective (toPinching (R := K)).appTop := by
  let φ := CommRingCat.ofHom (B (R := K)).val.toRingHom
  have he : (toPinching (R := K)).appTop =
      (Scheme.ΓSpecIso (.of (B (R := K)))).hom ≫ φ ≫
        (Scheme.ΓSpecIso (.of (Polynomial K))).inv := by
    simp [toPinching, φ]
  rw [he]
  exact (Scheme.ΓSpecIso (.of (Polynomial K))).symm.commRingCatIsoToRingEquiv.injective.comp
    (Subtype.val_injective.comp
      (Scheme.ΓSpecIso (.of (B (R := K)))).commRingCatIsoToRingEquiv.injective)

set_option backward.isDefEq.respectTransparency false in
/-- Every local-ring map is injective: the affine line is integral. -/
theorem stalkMap_injective (x : Spec (.of (Polynomial K))) :
    Function.Injective ((toPinching (R := K)).stalkMap x) := by
  apply stalkMap_injective_of_isAffine
  intro g h
  erw [TopCat.Presheaf.Γgerm, Scheme.Hom.germ_stalkMap_apply] at h
  have hg : (toPinching (R := K)).appTop g = 0 := by
    apply (germ_injective_of_isIntegral (Spec (.of (Polynomial K))) (U := ⊤) x trivial)
    simpa [Scheme.Hom.appTop] using h
  have hg' : g = 0 := appTop_injective (by simpa using hg)
  simp [hg']

/-- The pinching map is an epimorphism even against nonaffine targets. -/
instance toPinching_epi : Epi (toPinching (R := K)) := by
  apply CategoryTheory.Functor.epi_of_epi_map Scheme.forgetToLocallyRingedSpace
  apply CategoryTheory.Functor.epi_of_epi_map LocallyRingedSpace.forgetToSheafedSpace
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _ toPinching_surjective
  intro x
  exact ConcreteCategory.mono_of_injective _ (stalkMap_injective x)

/-- Two maps to an arbitrary scheme agree if they agree on the normalization. -/
theorem hom_ext {X : Scheme.{u}} (f g : Spec (.of (B (R := K))) ⟶ X)
    (h : toPinching ≫ f = toPinching ≫ g) : f = g :=
  (cancel_epi (toPinching (R := K))).mp h

end FLT.Mazur.OneGonDescentUniqueness
