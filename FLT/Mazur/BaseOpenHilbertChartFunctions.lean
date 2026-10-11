/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeEffectiveEpiSections
public import FLT.Mazur.BaseOpenHilbertRestrictedRelation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Effective scheme quotients and functions on base-local Hilbert charts

The actual base-local Hilbert parameter scheme is the scheme coequalizer of
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
  (d : ℕ) (V : Over (Spec (.of R))) [IsOpenImmersion V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

/-- The actual parameter map is an effective epimorphism of schemes. -/
instance baseOpenSourceParameter_effectiveEpi :
    EffectiveEpi (variableSourceParameter f hL d V c).left := inferInstance

/-- The base-local chart is the scheme coequalizer of the restricted original relation. -/
def baseOpenChartCoforkIsColimit :
    IsColimit (Cofork.ofπ (variableSourceParameter f hL d V c).left
      (congrArg Over.Hom.left (baseOpenRestricted_condition f hL d V c))) :=
  isColimitCoforkOfEffectiveEpi (variableSourceParameter f hL d V c).left _
    ((baseOpenRestricted_isPullback f hL d V c).map (Over.forget _)).isLimit

omit [IsOpenImmersion V.hom] in
/-- The smooth cover detects equality of actual chart functions. -/
theorem baseOpenChartFunctions_injective :
    Function.Injective (variableSourceParameter f hL d V c).left.appTop :=
  SchemeEffectiveEpiSections.appTop_injective _

/-- Compatible regular functions on the actual source intersection descend uniquely. -/
theorem baseOpenChartFunction_existsUnique
    (s : Γ((variableSourceIntersection f hL d V c).left, ⊤))
    (hs : (baseOpenRestrictedFst f hL d V c).left.appTop s =
      (baseOpenRestrictedSnd f hL d V c).left.appTop s) :
    ∃! t : Γ((variableHilbertTest f d V).left, ⊤),
      (variableSourceParameter f hL d V c).left.appTop t = s :=
  SchemeEffectiveEpiSections.sections_existsUnique
    (g := (variableSourceParameter f hL d V c).left)
    ((baseOpenRestricted_isPullback f hL d V c).map (Over.forget _)) s hs

/-- Functions on the chart satisfy exactly the original restricted relation equation. -/
theorem baseOpenChartFunction_iff (s : Γ((variableSourceIntersection f hL d V c).left, ⊤)) :
    (∃! t : Γ((variableHilbertTest f d V).left, ⊤),
      (variableSourceParameter f hL d V c).left.appTop t = s) ↔
    (baseOpenRestrictedFst f hL d V c).left.appTop s =
      (baseOpenRestrictedSnd f hL d V c).left.appTop s := by
  constructor
  · rintro ⟨t, rfl, _⟩
    exact congrArg (fun k : (baseOpenRestrictedRelation f hL d V c).left ⟶
      (variableHilbertTest f d V).left ↦ k.appTop t)
        (congrArg Over.Hom.left (baseOpenRestricted_condition f hL d V c))
  · exact baseOpenChartFunction_existsUnique f hL d V c s

/-- The actual chart ring is isomorphic to the restricted relation's invariant-function ring. -/
def baseOpenChartFunctionRingEquiv : Γ((variableHilbertTest f d V).left, ⊤) ≃+*
    SchemeEffectiveEpiSections.compatibleFunctions
      (baseOpenRestrictedFst f hL d V c).left (baseOpenRestrictedSnd f hL d V c).left :=
  SchemeEffectiveEpiSections.sectionsRingEquiv
    (g := (variableSourceParameter f hL d V c).left)
    ((baseOpenRestricted_isPullback f hL d V c).map (Over.forget _))

end FLT.Mazur.HilbertChart
