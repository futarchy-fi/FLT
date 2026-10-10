/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenAmbientNaturality

/-!
# The full universal family on the ambient Hilbert open

The identity parameter gives the actual universal ideal in the ambient open.
Its closed projection has finite locally free degree d, and every represented
full ideal is its actual arbitrary-scheme pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)

/-- The actual Hilbert support open's structure morphism to the coefficient scheme. -/
def openAmbientHilbertStructure :
    (ambientHilbertSupportOpen R I d K U).toScheme ⟶ Spec (.of R) :=
  (ambientHilbertSupportOpen R I d K U).ι ≫ ambientHilbertStructure R I d K

/-- The actual full universal family in the open ambient over its representing scheme. -/
def openAmbientUniversalFamily :
    OpenQuotientSchemeFamilies R I d K U (openAmbientHilbertStructure R I d K U) :=
  openAmbientSchemeClassification R I d K U (openAmbientHilbertStructure R I d K U)
    ⟨𝟙 _, Category.id_comp _⟩

/-- The universal ideal's actual closed projection has the requested finite locally free degree. -/
theorem openAmbientUniversalFamily_degree :
    FiniteLocallyFreeDegree ((openAmbientUniversalFamily R I d K U).val.subschemeι ≫
      (quotientRelativeOpen R I K U (openAmbientHilbertStructure R I d K U)).ι ≫
        pullback.fst _ _) d := (openAmbientUniversalFamily R I d K U).property

variable {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Every represented family is the actual pullback of the constructed universal family. -/
theorem openAmbientSchemeClassification_universalPullback
    (f : OpenAmbientSchemeParameters R I d K U s) :
    openQuotientSchemeFamilyBaseChange R I K U (openAmbientHilbertStructure R I d K U)
        s f.val f.property d (openAmbientUniversalFamily R I d K U) =
      openAmbientSchemeClassification R I d K U s f := by
  have h := openAmbientSchemeClassification_natural R I d K U
    (openAmbientHilbertStructure R I d K U) s f.val f.property
    ⟨𝟙 _, Category.id_comp _⟩
  have he : openAmbientSchemeParameterBaseChange R I d K U
      (openAmbientHilbertStructure R I d K U) s f.val f.property
        ⟨𝟙 _, Category.id_comp _⟩ = f := Subtype.ext (Category.comp_id _)
  rw [he] at h
  exact h.symm

/-- Classifying any actual open family pulls the full universal ideal back to the original ideal. -/
theorem openAmbientUniversalFamily_recovery (J : OpenQuotientSchemeFamilies R I d K U s) :
    openQuotientSchemeFamilyBaseChange R I K U (openAmbientHilbertStructure R I d K U) s
        ((openAmbientSchemeClassification R I d K U s).symm J).val
        ((openAmbientSchemeClassification R I d K U s).symm J).property d
        (openAmbientUniversalFamily R I d K U) = J := by
  rw [openAmbientSchemeClassification_universalPullback, Equiv.apply_symm_apply]

end FLT.Mazur.HilbertChart
