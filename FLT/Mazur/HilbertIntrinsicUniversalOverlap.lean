/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenAmbientOverlap

/-!
# Intrinsic universal ideals and their actual overlap compatibility

The identity parameter gives the full universal ideal on the intrinsic
ambient pullback. The constructed Hilbert overlap identifies the transported
source ideal with the actual pullback of the target universal ideal.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ) (K : Ideal (MvPolynomial I R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)

/-- The full universal ideal in the actual base change of the original ambient open. -/
def openIntrinsicUniversalFamily :
    RelativeIdealFamilies (quotientOriginalOpenStructure R I K U) d
      (openAmbientHilbertStructure R I d K U) :=
  openIntrinsicSchemeClassification R I d K U (openAmbientHilbertStructure R I d K U)
    ⟨𝟙 _, Category.id_comp _⟩

/-- The intrinsic universal family has the actual requested finite locally free degree. -/
theorem openIntrinsicUniversalFamily_degree :
    FiniteLocallyFreeDegree ((openIntrinsicUniversalFamily R I d K U).val.subschemeι ≫
      CategoryTheory.Limits.pullback.fst _ _) d :=
  (openIntrinsicUniversalFamily R I d K U).property

/-- Every full intrinsic classified ideal is a pullback of the constructed universal ideal. -/
theorem openIntrinsicUniversalFamily_pullback {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
    (p : OpenAmbientSchemeParameters R I d K U s) :
    relativeIdealFamilyBaseChange (quotientOriginalOpenStructure R I K U) d
        (openAmbientHilbertStructure R I d K U) s p.val p.property
          (openIntrinsicUniversalFamily R I d K U) =
      openIntrinsicSchemeClassification R I d K U s p := by
  have h := openIntrinsicSchemeClassification_natural R I d K U
    (openAmbientHilbertStructure R I d K U) s p.val p.property
    ⟨𝟙 _, Category.id_comp _⟩
  have hp : openAmbientSchemeParameterBaseChange R I d K U
      (openAmbientHilbertStructure R I d K U) s p.val p.property
        ⟨𝟙 _, Category.id_comp _⟩ = p := Subtype.ext (Category.comp_id _)
  rw [hp] at h
  exact h.symm

variable (I' : Type u) (K' : Ideal (MvPolynomial I' R))
variable (V : (Spec (.of (MvPolynomial I' R ⧸ K'))).Opens)
variable (e : U.toScheme ≅ V.toScheme)
variable (he : e.hom ≫ quotientOriginalOpenStructure R I' K' V =
  quotientOriginalOpenStructure R I K U)

/-- The actual overlap pulls the target universal ideal back to the transported source ideal. -/
theorem openIntrinsicUniversalFamily_overlap :
    relativeIdealFamilyBaseChange (quotientOriginalOpenStructure R I' K' V) d
        (openAmbientHilbertStructure R I' d K' V) (openAmbientHilbertStructure R I d K U)
        (openAmbientOverlapIso R I I' d K K' U V e he).hom
        (openAmbientOverlapIso_over R I I' d K K' U V e he)
        (openIntrinsicUniversalFamily R I' d K' V) =
      relativeIdealFamilyIsoEquiv e (quotientOriginalOpenStructure R I K U)
        (quotientOriginalOpenStructure R I' K' V) he
        (openAmbientHilbertStructure R I d K U) d (openIntrinsicUniversalFamily R I d K U) := by
  rw [openIntrinsicUniversalFamily_pullback R I' d K' V _
    ⟨(openAmbientOverlapIso R I I' d K K' U V e he).hom,
      openAmbientOverlapIso_over R I I' d K K' U V e he⟩]
  have hp : (⟨(openAmbientOverlapIso R I I' d K K' U V e he).hom,
      openAmbientOverlapIso_over R I I' d K K' U V e he⟩ :
        OpenAmbientSchemeParameters R I' d K' V (openAmbientHilbertStructure R I d K U)) =
      openAmbientOverlapParameters R I I' d K K' U V e he
        (openAmbientHilbertStructure R I d K U) ⟨𝟙 _, Category.id_comp _⟩ := by
    apply Subtype.ext
    rw [openAmbientOverlapIso_parameters, Category.id_comp]
  rw [hp, openAmbientOverlapParameters_family]
  rfl

end FLT.Mazur.HilbertChart
