/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanPathIsomorphisms

/-!
# Original restriction paths from principal chart coordinates

An actual chart isomorphism supplies its inverse. Localizing the other chart's
ambient map then constructs the restriction to their intersection, together
with its full ambient path equation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalOriginalRestrictionPaths

universe u v w z

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
  {B : Type w} [CommRing B] [Algebra R B]
  {D : Type z} [CommRing D] [Algebra R D]
  (r : A) (e : Localization.Away r ≃ₐ[R] B) (f : A →ₐ[R] D)

/-- Restrict the other ambient coordinate map to the principal source open. -/
def localized : Localization.Away r →ₐ[R] Localization.Away (f r) :=
  IsLocalization.Away.mapₐ _ _ f r

/-- Transfer this actual restriction through the given original chart isomorphism. -/
def restriction : B →ₐ[R] Localization.Away (f r) :=
  (localized r f).comp e.symm.toAlgHom

/-- The constructed restriction recovers the specified localized ambient map. -/
theorem restriction_coordinate : (restriction r e f).comp e.toAlgHom = localized r f := by
  apply AlgHom.ext
  intro x
  exact congrArg (localized r f) (e.symm_apply_apply x)

/-- The two actual restriction paths agree on the full ambient chart ring. -/
theorem restriction_ambient :
    ((restriction r e f).comp e.toAlgHom).comp (Algebra.algHom R A (Localization.Away r)) =
      (Algebra.algHom R D (Localization.Away (f r))).comp f := by
  rw [restriction_coordinate]
  apply AlgHom.ext
  intro x
  change localized r f (algebraMap A (Localization.Away r) x) =
    algebraMap D (Localization.Away (f r)) (f x)
  simp [localized, IsLocalization.Away.mapₐ, IsLocalization.Away.map]

/-- The original path equation also holds after any finite ambient presentation map. -/
theorem restriction_ambient_precomp {C : Type*} [CommRing C] [Algebra R C]
    (p : C →ₐ[R] A) :
    (((restriction r e f).comp e.toAlgHom).comp
      (Algebra.algHom R A (Localization.Away r))).comp p =
        ((Algebra.algHom R D (Localization.Away (f r))).comp f).comp p := by
  rw [restriction_ambient]

end FLT.Mazur.PrincipalOriginalRestrictionPaths
