/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmbientQuotientRelativeBaseChange
public import FLT.Mazur.HilbertAmbientSchemeClassification

/-!
# Naturality of affine quotient ambient Hilbert representation

Arbitrary scheme base change pulls back the actual quotient-ambient ideal
and composes its classifying parameter. Both directions of the representing
equivalence commute with this construction, with degree proved cartesianly.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (K : Ideal (MvPolynomial I R))
variable {X Y : Scheme.{u}} (s : X ⟶ Spec (.of R)) (t : Y ⟶ Spec (.of R))
variable (g : Y ⟶ X) (hg : g ≫ s = t)

/-- Actual base change of the full finite locally free family in the affine quotient ambient. -/
def quotientSchemeFamilyBaseChange (J : QuotientSchemeFamilies R I d K s) :
    QuotientSchemeFamilies R I d K t :=
  ⟨J.val.comap (quotientRelativeAmbientMap R I K s t g hg),
    ClosedIdealCover.restriction_degree J.val _
      (quotientRelativeAmbientMap_isPullback R I K s t g hg) d J.property⟩

/-- Base change of an actual ambient Hilbert parameter is composition of scheme morphisms. -/
def ambientSchemeParameterBaseChange (f : AmbientSchemeParameters R I d K s) :
    AmbientSchemeParameters R I d K t :=
  ⟨g ≫ f.val, by rw [Category.assoc, f.property, hg]⟩

/-- Forgetting the closed ambient condition commutes with the actual base-change morphism. -/
theorem ambientSchemeForget_baseChange (f : AmbientSchemeParameters R I d K s) :
    (ambientSchemeForget R I d K t (ambientSchemeParameterBaseChange R I d K s t g hg f)).val =
      g ≫ (ambientSchemeForget R I d K s f).val := Category.assoc _ _ _

/-- Equal scheme parameters over the base give identical full universal pullback ideals. -/
theorem polynomialSchemeParameterIdeal_congr
    (f₁ f₂ : Y ⟶ polynomialHilbertScheme R I d)
    (h₁ : f₁ ≫ polynomialHilbertStructure R I d = t)
    (h₂ : f₂ ≫ polynomialHilbertStructure R I d = t) (h : f₁ = f₂) :
    polynomialSchemeParameterIdeal R I d t f₁ h₁ =
      polynomialSchemeParameterIdeal R I d t f₂ h₂ := by
  subst f₂
  rfl

/-- The ambient Hilbert representing equivalence commutes with arbitrary scheme base change. -/
theorem ambientSchemeClassification_natural (f : AmbientSchemeParameters R I d K s) :
    ambientSchemeClassification R I d K t
        (ambientSchemeParameterBaseChange R I d K s t g hg f) =
      quotientSchemeFamilyBaseChange R I d K s t g hg
        (ambientSchemeClassification R I d K s f) := by
  apply Subtype.ext
  change (ambientSchemeClassification R I d K t _).val =
    (ambientSchemeClassification R I d K s f).val.comap _
  rw [ambientSchemeClassification_ideal, ambientSchemeClassification_ideal,
    ← Scheme.IdealSheafData.comap_comp, quotientRelativeAmbientMap_immersion,
    Scheme.IdealSheafData.comap_comp, polynomialSchemeParameterIdeal_baseChange]
  apply congrArg (fun J : (polynomialRelativeAmbient R I t).IdealSheafData ↦
    J.comap (quotientRelativeImmersion R I K t))
  exact polynomialSchemeParameterIdeal_congr R I d t _ _ _ _
    (ambientSchemeForget_baseChange R I d K s t g hg f)

/-- The actual classifying morphism of every quotient-ambient family commutes with base change. -/
theorem ambientSchemeClassification_symm_natural (J : QuotientSchemeFamilies R I d K s) :
    (ambientSchemeClassification R I d K t).symm
        (quotientSchemeFamilyBaseChange R I d K s t g hg J) =
      ambientSchemeParameterBaseChange R I d K s t g hg
        ((ambientSchemeClassification R I d K s).symm J) := by
  apply (ambientSchemeClassification R I d K t).injective
  rw [Equiv.apply_symm_apply, ambientSchemeClassification_natural, Equiv.apply_symm_apply]

end FLT.Mazur.HilbertChart
