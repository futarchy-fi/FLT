/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperSplitSectionRelativeCartier
public import FLT.Mazur.CartierAbelLocallySplit

/-!
# Proper relative Cartier sections and locally split direct-image lines

On an affine Noetherian base, residue acyclicity and geometric integrality
identify local splitting of the original direct-image map with regularity
and flatness of the full zero subscheme of the original tensor section.
The construction retains the base line and the section, not just their orbit.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperSectionSplittingCriterion
open FCurve ModuleSheafTensor CartierAbel SplitLineAffineNeighborhood
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (LineSectionBaseChange.residueAlgebraFiberLine f L z) (n + 1)))
  {B : S.Modules} (hB : LocallyFreeRankOne B)
  (s : Γ(tensor L ((pullback f).obj B), ⊤))

/-- Construct an actual relative section from local splitting, retaining its original data. -/
def relativeSection (hs : LocallySplit (twistedSectionPushforwardEquiv f L hB s)) :
    RelativeSection f L hL := by
  obtain ⟨hm, hC⟩ :=
    ProperSplitSectionRelativeCartier.regular_and_relativeCartier f L hL hV hB s hs
  exact ⟨⟨⟨B, hB⟩, s, hm⟩, hC.2⟩

include hV in
/-- Local splitting is equivalent to the regular full relative Cartier condition. -/
theorem locallySplit_iff [Surjective f] :
    LocallySplit (twistedSectionPushforwardEquiv f L hB s) ↔
      Mono (globalSectionHom _ s) ∧
        RelativeEffectiveCartier f (lineSectionZeroIdeal (hL.tensor (hB.pullback f)) s) := by
  constructor
  · exact ProperSplitSectionRelativeCartier.regular_and_relativeCartier f L hL hV hB s
  · rintro ⟨hm, hC⟩
    let t : RelativeSection f L hL := ⟨⟨⟨B, hB⟩, s, hm⟩, hC.2⟩
    exact relativeSection_proper_directImage_locallySplit f L hL hV t

end FLT.Mazur.ProperSectionSplittingCriterion
