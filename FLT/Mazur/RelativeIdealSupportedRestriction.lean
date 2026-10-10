/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealOpenExtension

/-!
# Restriction of supported full relative ideal families

Support containment in an original ambient open allows restriction of a full
finite locally free family without changing its degree. Extending that
restriction recovers the entire original ideal, including nilpotents.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData FLT.Mazur.FCurve FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.ClosedIdealCover

set_option backward.isDefEq.respectTransparency false

variable {A B S X : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S)
variable (i : A ⟶ B) [IsOpenImmersion i] (hi : i ≫ b = a)
variable (s : X ⟶ S) (d : ℕ) (J : RelativeIdealFamilies b d s)
variable (hJ : Set.range J.val.subschemeι ⊆ Set.range (relativeIdealAmbientHom a b i hi s))

/-- A full family supported in the original open restricts with the same actual degree. -/
def relativeIdealFamilyRestriction : RelativeIdealFamilies a d s := by
  refine ⟨J.val.comap (relativeIdealAmbientHom a b i hi s), ?_⟩
  have h := J.property.of_overIso
    (supportedIdealFamilyIso (relativeIdealAmbientHom a b i hi s)
      (pullback.fst s b) J.val hJ).symm
  rwa [relativeIdealAmbientHom_fst] at h

/-- Supported restriction uses the actual full ideal pullback. -/
theorem relativeIdealFamilyRestriction_ideal :
    (relativeIdealFamilyRestriction a b i hi s d J hJ).val =
      J.val.comap (relativeIdealAmbientHom a b i hi s) := rfl

variable [IsSeparated b]

/-- Extending a supported restriction recovers the entire original ambient family. -/
theorem relativeIdealFamilyExtension_restriction :
    relativeIdealFamilyExtension a b i hi s d
      (relativeIdealFamilyRestriction a b i hi s d J hJ) = J := by
  apply Subtype.ext
  exact open_map_comap (relativeIdealAmbientHom a b i hi s) J.val hJ

/-- Restricting an extended full family recovers the entire original open family. -/
theorem relativeIdealFamilyRestriction_extension (K : RelativeIdealFamilies a d s) :
    relativeIdealFamilyRestriction a b i hi s d
      (relativeIdealFamilyExtension a b i hi s d K)
      (relativeIdealFamilyExtension_support a b i hi s d K) = K := by
  apply Subtype.ext
  exact relativeIdealFamilyExtension_restrict a b i hi s d K

end FLT.Mazur.ClosedIdealCover
