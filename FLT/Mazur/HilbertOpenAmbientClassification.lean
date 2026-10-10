/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenAmbientFamilies
public import FLT.Mazur.HilbertAmbientSupportFactorization
public import FLT.Mazur.OpenSchemeParameters

/-!
# Hilbert representation for an actual open affine ambient

The exact universal support open represents all finite locally free closed
ideal families in the actual ambient open over every test scheme. The input
contains only the full ideal and its degree; extension, support containment,
and the parameter lift are constructed. Both inverse laws retain full ideals.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)
variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Actual parameters of the constructed Hilbert support open over the coefficient base. -/
def OpenAmbientSchemeParameters :=
  { f : X ⟶ (ambientHilbertSupportOpen R I d K U).toScheme //
    f ≫ (ambientHilbertSupportOpen R I d K U).ι ≫ ambientHilbertStructure R I d K = s }

/-- Full ambient classification identifies precisely the supported parameters and families. -/
def supportedAmbientSchemeClassification :
    { f : AmbientSchemeParameters R I d K s //
      Set.range f.val ⊆ ambientHilbertSupportOpen R I d K U } ≃
      SupportedQuotientSchemeFamilies R I d K U s where
  toFun f := ⟨ambientSchemeClassification R I d K s f.val,
    (range_subset_ambientHilbertSupportOpen_iff R I d K U s f.val).mp f.property⟩
  invFun J := ⟨(ambientSchemeClassification R I d K s).symm J.val, by
    apply (range_subset_ambientHilbertSupportOpen_iff R I d K U s _).mpr
    rw [Equiv.apply_symm_apply]
    exact J.property⟩
  left_inv f := Subtype.ext (Equiv.symm_apply_apply _ f.val)
  right_inv J := Subtype.ext (Equiv.apply_symm_apply _ J.val)

/-- The constructed Hilbert support open represents all actual families in the ambient open. -/
def openAmbientSchemeClassification :
    OpenAmbientSchemeParameters R I d K U s ≃ OpenQuotientSchemeFamilies R I d K U s :=
  (openSchemeParameterEquiv (ambientHilbertStructure R I d K)
    (ambientHilbertSupportOpen R I d K U) s).trans
    ((supportedAmbientSchemeClassification R I d K U s).trans
      (openQuotientSchemeFamilyEquiv R I d K U s).symm)

/-- The represented open-family ideal is the full restriction of the ambient represented ideal. -/
theorem openAmbientSchemeClassification_ideal (f : OpenAmbientSchemeParameters R I d K U s) :
    (openAmbientSchemeClassification R I d K U s f).val =
      (ambientSchemeClassification R I d K s
        ⟨f.val ≫ (ambientHilbertSupportOpen R I d K U).ι,
          (Category.assoc _ _ _).trans f.property⟩).val.comap
        (quotientRelativeOpen R I K U s).ι := rfl

/-- Classifying recovers the full original ideal family on the ambient open. -/
theorem openAmbientSchemeClassification_recovery (J : OpenQuotientSchemeFamilies R I d K U s) :
    openAmbientSchemeClassification R I d K U s
      ((openAmbientSchemeClassification R I d K U s).symm J) = J :=
  Equiv.apply_symm_apply _ J

/-- Pulling back and classifying recovers the actual morphism to the Hilbert support open. -/
theorem openAmbientSchemeClassification_parameter (f : OpenAmbientSchemeParameters R I d K U s) :
    (openAmbientSchemeClassification R I d K U s).symm
      (openAmbientSchemeClassification R I d K U s f) = f := Equiv.symm_apply_apply _ f

end FLT.Mazur.HilbertChart
