/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertSplitQuotient
public import FLT.Mazur.SchemeEffectiveEpiSections
public import Mathlib.CategoryTheory.EffectiveEpi.Comp

/-!
# Scheme effectivity and invariant functions for split full Hilbert quotients

The actual parameter comparison is an effective epimorphism of schemes.
Its coequalizer uses the original full Picard relation, and its regular
functions are exactly the functions invariant under that relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  [IsOpenImmersion V.hom] (c : (relativeFppfSheaf f).obj.obj (op V))
  (s : V ⟶ W) (hs : s ≫ b = 𝟙 V)
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c

omit [IsOpenImmersion V.hom] in
include hs in
/-- The actual parameter comparison is an effective epimorphism of schemes. -/
theorem variableHilbertSplitChange_effectiveEpi :
    EffectiveEpi (baseMarkedChartChange f b d).left := by
  let _ : IsSplitEpi (baseMarkedChartChange f b d).left :=
    IsSplitEpi.mk' ⟨(baseMarkedChartChange f s d).left,
      congrArg Over.Hom.left (variableHilbertChange_section f d b s hs)⟩
  infer_instance

/-- The constructed target scheme is the coequalizer of the FULL original chart relation. -/
def variableHilbertSplitCoforkIsColimit :
    IsColimit (Cofork.ofπ (baseMarkedChartChange f b d).left
      (congrArg Over.Hom.left (variableHilbertChange_condition f hL d b c))) := by
  let _ := variableHilbertSplitChange_effectiveEpi f d b s hs
  exact isColimitCoforkOfEffectiveEpi (baseMarkedChartChange f b d).left _
    ((variableHilbertChange_isPullback f hL d b c).map (Over.forget _)).isLimit

include hs in
/-- Every regular function satisfying the original full relation descends uniquely. -/
theorem variableHilbertSplitFunction_existsUnique
    (t : Γ((variableHilbertTest f d W).left, ⊤))
    (ht : (variableChartRelationFst f hL d W cW).left.appTop t =
      (variableChartRelationSnd f hL d W cW).left.appTop t) :
    ∃! u : Γ((variableHilbertTest f d V).left, ⊤),
      (baseMarkedChartChange f b d).left.appTop u = t := by
  let _ := variableHilbertSplitChange_effectiveEpi f d b s hs
  exact SchemeEffectiveEpiSections.sections_existsUnique
    (g := (baseMarkedChartChange f b d).left)
    ((variableHilbertChange_isPullback f hL d b c).map (Over.forget _)) t ht

/-- Functions on the quotient are precisely invariant functions on the original source. -/
def variableHilbertSplitFunctionRingEquiv :
    Γ((variableHilbertTest f d V).left, ⊤) ≃+*
      SchemeEffectiveEpiSections.compatibleFunctions
        (variableChartRelationFst f hL d W cW).left
        (variableChartRelationSnd f hL d W cW).left := by
  let _ := variableHilbertSplitChange_effectiveEpi f d b s hs
  exact SchemeEffectiveEpiSections.sectionsRingEquiv
    (g := (baseMarkedChartChange f b d).left)
    ((variableHilbertChange_isPullback f hL d b c).map (Over.forget _))

end FLT.Mazur.HilbertChart
