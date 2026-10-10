/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionIdealDegree
public import FLT.Mazur.HilbertAmbientFamilySupport

/-!
# Actual families in an open of an affine quotient ambient

The relative open is the inverse image of the original ambient open under
the actual base-change projection. Its finite locally free closed families
are exactly the full closed families of the containing affine ambient whose
whole support lies in the original open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- The actual open ambient over the arbitrary test base. -/
def quotientRelativeOpen : (quotientRelativeAmbient R I K s).Opens :=
  pullback.snd s (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K)))) ⁻¹ᵁ U

/-- All full ideal families of the requested degree in the actual relative ambient open. -/
def OpenQuotientSchemeFamilies :=
  { J : (quotientRelativeOpen R I K U s).toScheme.IdealSheafData //
    FiniteLocallyFreeDegree
      (J.subschemeι ≫ (quotientRelativeOpen R I K U s).ι ≫ pullback.fst _ _) d }

/-- Families in the containing ambient whose entire actual family lies in the given open. -/
def SupportedQuotientSchemeFamilies :=
  { J : QuotientSchemeFamilies R I d K s //
    Set.range (quotientFamilyAmbientMap R I d K s J) ⊆ U }

/-- Relative-open containment is exactly containment of the actual map to the original ambient. -/
theorem quotientFamily_range_relativeOpen_iff (J : QuotientSchemeFamilies R I d K s) :
    Set.range J.val.subschemeι ⊆ Set.range (quotientRelativeOpen R I K U s).ι ↔
      Set.range (quotientFamilyAmbientMap R I d K s J) ⊆ U := by
  rw [Scheme.Opens.range_ι]
  constructor
  · rintro h _ ⟨z, rfl⟩
    exact h ⟨z, rfl⟩
  · rintro h _ ⟨z, rfl⟩
    exact h ⟨z, rfl⟩

/-- Extension identifies actual open families with all supported containing-ambient families. -/
def openQuotientSchemeFamilyEquiv :
    OpenQuotientSchemeFamilies R I d K U s ≃ SupportedQuotientSchemeFamilies R I d K U s :=
  (openIdealFamilyEquiv (quotientRelativeOpen R I K U s).ι (pullback.fst _ _) d).trans
    { toFun := fun J ↦ ⟨⟨J.val, J.property.1⟩,
        (quotientFamily_range_relativeOpen_iff R I d K U s _).mp J.property.2⟩
      invFun := fun J ↦ ⟨J.val.val, J.val.property,
        (quotientFamily_range_relativeOpen_iff R I d K U s _).mpr J.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/-- Open-family extension retains the entire ideal of its actual closed immersion. -/
theorem openQuotientSchemeFamilyEquiv_ideal (J : OpenQuotientSchemeFamilies R I d K U s) :
    (openQuotientSchemeFamilyEquiv R I d K U s J).val.val =
      J.val.map (quotientRelativeOpen R I K U s).ι := rfl

/-- The inverse comparison restricts the entire supported ideal to the actual relative open. -/
theorem openQuotientSchemeFamilyEquiv_symm_ideal
    (J : SupportedQuotientSchemeFamilies R I d K U s) :
    ((openQuotientSchemeFamilyEquiv R I d K U s).symm J).val =
      J.val.val.comap (quotientRelativeOpen R I K U s).ι := rfl

end FLT.Mazur.HilbertChart
