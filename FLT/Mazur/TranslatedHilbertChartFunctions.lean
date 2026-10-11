/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeEffectiveEpiSections
public import FLT.Mazur.TranslatedHilbertRestrictedRelation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Effective scheme quotients and functions on translated Hilbert charts

The actual translated Hilbert parameter scheme is the scheme coequalizer of
the restricted original relation. Its global regular functions are exactly
the compatible functions on the source intersection. This does not yet
identify the invariant sheaf on all quotient opens.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (i : TranslatedHilbertIndex f)

/-- The actual parameter map is an effective epimorphism of schemes. -/
instance translatedSourceParameter_effectiveEpi :
    EffectiveEpi (translatedSourceParameter f hL i).left := inferInstance

/-- The translated chart is the scheme coequalizer of the restricted original relation. -/
def translatedChartCoforkIsColimit :
    IsColimit (Cofork.ofπ (translatedSourceParameter f hL i).left
      (congrArg Over.Hom.left (translatedRestricted_condition f hL i))) :=
  isColimitCoforkOfEffectiveEpi (translatedSourceParameter f hL i).left _
    ((translatedRestricted_isPullback f hL i).map (Over.forget _)).isLimit

/-- The smooth cover detects equality of actual chart functions. -/
theorem translatedChartFunctions_injective :
    Function.Injective (translatedSourceParameter f hL i).left.appTop :=
  SchemeEffectiveEpiSections.appTop_injective _

/-- Compatible regular functions on the actual source intersection descend uniquely. -/
theorem translatedChartFunction_existsUnique
    (s : Γ((translatedSourceIntersection f hL i).left, ⊤))
    (hs : (translatedRestrictedFst f hL i).left.appTop s =
      (translatedRestrictedSnd f hL i).left.appTop s) :
    ∃! t : Γ((acyclicHilbertTest f i.1).left, ⊤),
      (translatedSourceParameter f hL i).left.appTop t = s :=
  SchemeEffectiveEpiSections.sections_existsUnique
    (g := (translatedSourceParameter f hL i).left)
    ((translatedRestricted_isPullback f hL i).map (Over.forget _)) s hs

/-- Functions on the chart satisfy exactly the original restricted relation equation. -/
theorem translatedChartFunction_iff (s : Γ((translatedSourceIntersection f hL i).left, ⊤)) :
    (∃! t : Γ((acyclicHilbertTest f i.1).left, ⊤),
      (translatedSourceParameter f hL i).left.appTop t = s) ↔
    (translatedRestrictedFst f hL i).left.appTop s =
      (translatedRestrictedSnd f hL i).left.appTop s := by
  constructor
  · rintro ⟨t, rfl, _⟩
    exact congrArg (fun k : (translatedRestrictedRelation f hL i).left ⟶
      (acyclicHilbertTest f i.1).left ↦ k.appTop t)
        (congrArg Over.Hom.left (translatedRestricted_condition f hL i))
  · exact translatedChartFunction_existsUnique f hL i s

/-- The actual chart ring is isomorphic to the restricted relation's invariant-function ring. -/
def translatedChartFunctionRingEquiv : Γ((acyclicHilbertTest f i.1).left, ⊤) ≃+*
    SchemeEffectiveEpiSections.compatibleFunctions
      (translatedRestrictedFst f hL i).left (translatedRestrictedSnd f hL i).left :=
  SchemeEffectiveEpiSections.sectionsRingEquiv
    (g := (translatedSourceParameter f hL i).left)
    ((translatedRestricted_isPullback f hL i).map (Over.forget _))

end FLT.Mazur.HilbertChart
