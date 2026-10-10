/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertOpenAmbientClassification
public import FLT.Mazur.HilbertOpenAmbientBaseChange

/-!
# Naturality of the open ambient Hilbert representation

The representing equivalence commutes with arbitrary scheme base change of
the actual full ideals. The inverse classifying morphism consequently
commutes with base change as well.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable (U : (Spec (.of (MvPolynomial I R ⧸ K))).Opens)
variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R)) (t : Y ⟶ Spec (.of R))
variable (g : Y ⟶ X) (hg : g ≫ s = t)

/-- Forget an actual open parameter by composing its morphism with the open immersion. -/
def openAmbientSchemeForget (f : OpenAmbientSchemeParameters R I d K U s) :
    AmbientSchemeParameters R I d K s :=
  ⟨f.val ≫ (ambientHilbertSupportOpen R I d K U).ι,
    (Category.assoc _ _ _).trans f.property⟩

/-- Base change of a parameter in the actual Hilbert open is precomposition. -/
def openAmbientSchemeParameterBaseChange (f : OpenAmbientSchemeParameters R I d K U s) :
    OpenAmbientSchemeParameters R I d K U t :=
  ⟨g ≫ f.val, by rw [Category.assoc, f.property, hg]⟩

/-- Forgetting an open parameter commutes with its actual base-change morphism. -/
theorem openAmbientSchemeForget_baseChange (f : OpenAmbientSchemeParameters R I d K U s) :
    openAmbientSchemeForget R I d K U t
        (openAmbientSchemeParameterBaseChange R I d K U s t g hg f) =
      ambientSchemeParameterBaseChange R I d K s t g hg
        (openAmbientSchemeForget R I d K U s f) :=
  Subtype.ext (Category.assoc _ _ _)

/-- Representation on the ambient open commutes with arbitrary pullback of the full ideal. -/
theorem openAmbientSchemeClassification_natural (f : OpenAmbientSchemeParameters R I d K U s) :
    openAmbientSchemeClassification R I d K U t
        (openAmbientSchemeParameterBaseChange R I d K U s t g hg f) =
      openQuotientSchemeFamilyBaseChange R I K U s t g hg d
        (openAmbientSchemeClassification R I d K U s f) := by
  apply Subtype.ext
  change (ambientSchemeClassification R I d K t
      (openAmbientSchemeForget R I d K U t
        (openAmbientSchemeParameterBaseChange R I d K U s t g hg f))).val.comap _ =
    ((ambientSchemeClassification R I d K s
      (openAmbientSchemeForget R I d K U s f)).val.comap _).comap _
  rw [← Scheme.IdealSheafData.comap_comp, quotientRelativeOpenMap_ι,
    Scheme.IdealSheafData.comap_comp, openAmbientSchemeForget_baseChange,
    ambientSchemeClassification_natural]
  rfl

/-- The actual classifying morphism of an open family commutes with every base change. -/
theorem openAmbientSchemeClassification_symm_natural
    (J : OpenQuotientSchemeFamilies R I d K U s) :
    (openAmbientSchemeClassification R I d K U t).symm
        (openQuotientSchemeFamilyBaseChange R I K U s t g hg d J) =
      openAmbientSchemeParameterBaseChange R I d K U s t g hg
        ((openAmbientSchemeClassification R I d K U s).symm J) := by
  apply (openAmbientSchemeClassification R I d K U t).injective
  rw [Equiv.apply_symm_apply, openAmbientSchemeClassification_natural, Equiv.apply_symm_apply]

end FLT.Mazur.HilbertChart
