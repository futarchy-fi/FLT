/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperGlobalSplitDirectImageSections
public import FLT.Mazur.ProperLineChartFiberVanishing

/-!
# Relative Cartier sections on a locally Noetherian changed base

The original family's residue acyclicity supplies all affine-chart
hypotheses of the global criterion. A retained split direct-image map thus
constructs a regular section with flat full zero divisor on the changed family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
  TwistedSection.toDirectImage
variable {P X T S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  [IsLocallyNoetherian T] {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f]
  (h : IsPullback p q f g) (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

/-- Construct the retained relative section on a locally Noetherian changed base. -/
@[irreducible] def SplitDirectImageSection.toChangedBaseRelative
    (a : SplitDirectImageSection q ((pullback p).obj L)) :
    RelativeSection q ((pullback p).obj L) (hL.pullback p) := by
  letI : IsProper q := MorphismProperty.of_isPullback h inferInstance
  letI : Flat q := MorphismProperty.of_isPullback h inferInstance
  letI : GeometricallyIntegral q := MorphismProperty.of_isPullback h inferInstance
  letI (V : T.affineOpens) : IsNoetherianRing Γ(V.1.toScheme, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top V.1.toScheme⟩
  exact a.toGlobalRelative q _ (hL.pullback p) (fun V : T.affineOpens ↦ V.1)
    (fun V ↦ open_residue_fiber_vanishing h L hL hV V.1) (iSup_affineOpens_eq_top T)

/-- The construction keeps its original base line without choosing new charts for it. -/
lemma SplitDirectImageSection.toChangedBaseRelative_baseLine
    (a : SplitDirectImageSection q ((pullback p).obj L)) :
    (a.toChangedBaseRelative h L hL hV).val.baseLine = a.baseLine := by
  unfold SplitDirectImageSection.toChangedBaseRelative
  rfl

/-- The constructed section recovers the actual original direct-image inclusion. -/
lemma SplitDirectImageSection.toChangedBaseRelative_map
    (a : SplitDirectImageSection q ((pullback p).obj L)) :
    HEq (twistedSectionPushforwardEquiv q ((pullback p).obj L)
      (a.toChangedBaseRelative h L hL hV).val.baseLine.property
      (a.toChangedBaseRelative h L hL hV).val.section_) a.map := by
  unfold SplitDirectImageSection.toChangedBaseRelative
  exact heq_of_eq
    ((twistedSectionPushforwardEquiv q _ a.baseLine.property).apply_symm_apply a.map)

end FLT.Mazur.CartierAbel
