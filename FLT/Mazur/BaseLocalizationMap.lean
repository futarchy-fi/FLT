/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Basic

/-!
# Localization maps retaining the original scalar multiplicative set

Compatible ring maps induce maps between localizations at images of the same
original multiplicative set. This includes independently presented target
scalar maps, as needed for the two endpoints of a full mixed relation.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.BaseLocalizationMap
variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  (M : Submonoid R) (α : R →+* A) (γ : R →+* B) (φ : A →+* B)
  (h : ∀ x, φ (α x) = γ x)

include h in
/-- The original scalar compatibility sends every allowed denominator to an allowed one. -/
theorem map_le_comap : M.map α.toMonoidHom ≤ (M.map γ.toMonoidHom).comap φ := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx, (h x).symm⟩

/-- The induced map uses the original multiplicative set in both coefficient rings. -/
def map : Localization (M.map α.toMonoidHom) →+* Localization (M.map γ.toMonoidHom) :=
  IsLocalization.map _ φ (map_le_comap M α γ φ h)

/-- The induced map retains every original coefficient exactly. -/
theorem map_algebraMap (a : A) :
    map M α γ φ h (algebraMap _ _ a) = algebraMap _ _ (φ a) :=
  IsLocalization.map_eq _ a

end FLT.Mazur.BaseLocalizationMap
