/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenIntrinsicClassification
public import FLT.Mazur.HilbertOpenAmbientUniversalFamily
public import FLT.Mazur.RelativeIdealFamilyIsomorphism
public import FLT.Mazur.SchemeParameterEquivalence

/-!
# Actual Hilbert overlap isomorphisms from isomorphic ambient opens

An actual isomorphism over the coefficient base between opens in two affine
quotient ambients gives an isomorphism of their constructed Hilbert support
opens. It is obtained from full intrinsic family classification, not from
pointwise reduced supports. No parameter-scheme comparison is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.OpenIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I I' : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R)) (K' : Ideal (MvPolynomial I' R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)
variable (V : (Spec (.of (MvPolynomial I' R ⧸ K'))).Opens)
variable (e : U.toScheme ≅ V.toScheme)
variable (he : e.hom ≫ quotientOriginalOpenStructure R I' K' V =
  quotientOriginalOpenStructure R I K U)
variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R))

/-- Identify all parameters of the two Hilbert support opens through their actual full families. -/
def openAmbientOverlapParameters :
    OpenAmbientSchemeParameters R I d K U s ≃ OpenAmbientSchemeParameters R I' d K' V s :=
  (openIntrinsicSchemeClassification R I d K U s).trans
    ((relativeIdealFamilyIsoEquiv e (quotientOriginalOpenStructure R I K U)
      (quotientOriginalOpenStructure R I' K' V) he s d).trans
        (openIntrinsicSchemeClassification R I' d K' V s).symm)

/-- The parameter comparison recovers precisely the transported full intrinsic ideal family. -/
theorem openAmbientOverlapParameters_family (f : OpenAmbientSchemeParameters R I d K U s) :
    openIntrinsicSchemeClassification R I' d K' V s
        (openAmbientOverlapParameters R I I' d K K' U V e he s f) =
      relativeIdealFamilyIsoEquiv e (quotientOriginalOpenStructure R I K U)
        (quotientOriginalOpenStructure R I' K' V) he s d
        (openIntrinsicSchemeClassification R I d K U s f) :=
  Equiv.apply_symm_apply _ _

/-- The overlap parameter comparison commutes with arbitrary test-scheme morphisms. -/
theorem openAmbientOverlapParameters_natural (t : Y ⟶ Spec (.of R))
    (g : Y ⟶ X) (hg : g ≫ s = t) (f : OpenAmbientSchemeParameters R I d K U s) :
    openAmbientOverlapParameters R I I' d K K' U V e he t
        (openAmbientSchemeParameterBaseChange R I d K U s t g hg f) =
      openAmbientSchemeParameterBaseChange R I' d K' V s t g hg
        (openAmbientOverlapParameters R I I' d K K' U V e he s f) := by
  change (openIntrinsicSchemeClassification R I' d K' V t).symm
      (relativeIdealFamilyIsoEquiv e _ _ he t d
        (openIntrinsicSchemeClassification R I d K U t _)) = _
  rw [openIntrinsicSchemeClassification_natural, relativeIdealFamilyIsoEquiv_natural,
    openIntrinsicSchemeClassification_symm_natural]
  rfl

/-- Actual isomorphic ambient opens induce actual isomorphic Hilbert support opens. -/
def openAmbientOverlapIso :
    (ambientHilbertSupportOpen R I d K U).toScheme ≅
      (ambientHilbertSupportOpen R I' d K' V).toScheme :=
  schemeParameterEquivIso (openAmbientHilbertStructure R I d K U)
    (openAmbientHilbertStructure R I' d K' V)
    (fun s ↦ openAmbientOverlapParameters R I I' d K K' U V e he s)
    (fun s t g hg f ↦ congrArg Subtype.val
      (openAmbientOverlapParameters_natural R I I' d K K' U V e he s t g hg f))

/-- The constructed overlap isomorphism retains the actual coefficient-base structure. -/
theorem openAmbientOverlapIso_over :
    (openAmbientOverlapIso R I I' d K K' U V e he).hom ≫
        openAmbientHilbertStructure R I' d K' V = openAmbientHilbertStructure R I d K U :=
  schemeParameterEquivMap_over _ _ _

/-- On every test scheme, the actual overlap morphism induces the full-family comparison. -/
theorem openAmbientOverlapIso_parameters (f : OpenAmbientSchemeParameters R I d K U s) :
    (openAmbientOverlapParameters R I I' d K K' U V e he s f).val =
      f.val ≫ (openAmbientOverlapIso R I I' d K K' U V e he).hom :=
  schemeParameterEquiv_apply _ _ _
    (fun s t g hg f ↦ congrArg Subtype.val
      (openAmbientOverlapParameters_natural R I I' d K K' U V e he s t g hg f)) s f

end FLT.Mazur.HilbertChart
