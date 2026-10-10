/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenAmbientCartesian
public import FLT.Mazur.HilbertOpenAmbientNaturality

/-!
# Intrinsic Hilbert representation on an affine ambient open

The Hilbert support open represents full ideal families in the actual
scheme pullback of the original ambient open. The comparison of ambient
models and the representing equivalence are natural in every test scheme.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)
variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R)) (t : Y ⟶ Spec (.of R))
variable (g : Y ⟶ X) (hg : g ≫ s = t)

/-- Base change of the relative open preserves its actual map to the original open. -/
theorem quotientRelativeOpenMap_original :
    quotientRelativeOpenMap R I K U s t g hg ≫ quotientRelativeOpenOriginalMap R I K U s =
      quotientRelativeOpenOriginalMap R I K U t := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, quotientRelativeOpenOriginalMap_ι,
    ← Category.assoc, quotientRelativeOpenMap_ι, Category.assoc,
    quotientRelativeAmbientMap_snd, quotientRelativeOpenOriginalMap_ι]

/-- The actual pullback comparison commutes with every morphism of scheme bases. -/
theorem quotientRelativeOpenIso_natural :
    (quotientRelativeOpenIso R I K U t).hom ≫
        relativeIdealAmbientMap (quotientOriginalOpenStructure R I K U) s t g hg =
      quotientRelativeOpenMap R I K U s t g hg ≫ (quotientRelativeOpenIso R I K U s).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, relativeIdealAmbientMap_fst,
      quotientRelativeOpenIso_hom_fst, quotientRelativeOpenIso_hom_fst_assoc,
      quotientRelativeOpenMap_ι_assoc, quotientRelativeAmbientMap_fst]
  · simp only [Category.assoc, relativeIdealAmbientMap_snd,
      quotientRelativeOpenIso_hom_snd, quotientRelativeOpenMap_original]

/-- Identifying intrinsic and relative-open full ideal families commutes with actual base change. -/
theorem openQuotientIntrinsicFamilyEquiv_natural (J : OpenQuotientSchemeFamilies R I d K U s) :
    openQuotientIntrinsicFamilyEquiv R I K U t d
        (openQuotientSchemeFamilyBaseChange R I K U s t g hg d J) =
      relativeIdealFamilyBaseChange (quotientOriginalOpenStructure R I K U) d s t g hg
        (openQuotientIntrinsicFamilyEquiv R I K U s d J) := by
  apply Subtype.ext
  exact idealFamilyIso_comap (quotientRelativeOpenIso R I K U s)
    (quotientRelativeOpenIso R I K U t) _ _
    (quotientRelativeOpenIso_natural R I K U s t g hg) J.val

/-- The Hilbert support open represents all intrinsic full ideal families on the ambient open. -/
def openIntrinsicSchemeClassification :
    OpenAmbientSchemeParameters R I d K U s ≃
      RelativeIdealFamilies (quotientOriginalOpenStructure R I K U) d s :=
  (openAmbientSchemeClassification R I d K U s).trans
    (openQuotientIntrinsicFamilyEquiv R I K U s d)

/-- Intrinsic Hilbert classification on the actual open scheme is natural in every test base. -/
theorem openIntrinsicSchemeClassification_natural
    (f : OpenAmbientSchemeParameters R I d K U s) :
    openIntrinsicSchemeClassification R I d K U t
        (openAmbientSchemeParameterBaseChange R I d K U s t g hg f) =
      relativeIdealFamilyBaseChange (quotientOriginalOpenStructure R I K U) d s t g hg
        (openIntrinsicSchemeClassification R I d K U s f) := by
  change openQuotientIntrinsicFamilyEquiv R I K U t d
      (openAmbientSchemeClassification R I d K U t _) = _
  rw [openAmbientSchemeClassification_natural, openQuotientIntrinsicFamilyEquiv_natural]
  rfl

/-- The inverse intrinsic classifying morphism also commutes with arbitrary scheme base change. -/
theorem openIntrinsicSchemeClassification_symm_natural
    (J : RelativeIdealFamilies (quotientOriginalOpenStructure R I K U) d s) :
    (openIntrinsicSchemeClassification R I d K U t).symm
        (relativeIdealFamilyBaseChange (quotientOriginalOpenStructure R I K U) d s t g hg J) =
      openAmbientSchemeParameterBaseChange R I d K U s t g hg
        ((openIntrinsicSchemeClassification R I d K U s).symm J) := by
  apply (openIntrinsicSchemeClassification R I d K U t).injective
  rw [Equiv.apply_symm_apply, openIntrinsicSchemeClassification_natural, Equiv.apply_symm_apply]

end FLT.Mazur.HilbertChart
