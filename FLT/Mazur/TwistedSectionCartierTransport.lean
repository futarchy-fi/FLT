/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TwistedSectionPullbackMonicity
public import FLT.Mazur.LineSectionZeroIdealOrbits

/-!
# Full relative Cartier ideals under the twisted-section comparison

The tensor-square comparison preserves the full zero ideal, even before
regularity is known. Thus a local Cartier criterion for the transported
section applies to the unmodified sheaf pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.TwistedSectionPullbackMonicity
open FCurve ModuleSheafTensor TwistedSectionBaseChangeRegularity
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] tensor TwistedSectionBaseChangeRegularity.section_ sectionIso
variable {P X T S : Scheme.{0}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) (L : X.Modules) {B : S.Modules}
  (hL : LocallyFreeRankOne L) (hB : LocallyFreeRankOne B)
  (s : Γ(tensor L ((pullback f).obj B), ⊤))

/-- The tensor-square transport preserves every equation of the original zero subscheme. -/
lemma sectionIso_zeroIdeal :
    lineSectionZeroIdeal ((hL.tensor (hB.pullback f)).pullback p) (pullGlobal p _ s) =
      lineSectionZeroIdeal ((hL.pullback p).tensor ((hB.pullback g).pullback q))
        (section_ p q f g w L s) :=
  lineSectionZeroIdeal_eq_of_iso _ _ (sectionIso p q f g w L) _ _
    (sectionIso_section p q f g w L s)

/-- Relative Cartier regularity can be checked after the actual tensor-square transport. -/
theorem relativeCartier_iff :
    (Mono (globalSectionHom _ (section_ p q f g w L s)) ∧
      RelativeEffectiveCartier q
        (lineSectionZeroIdeal ((hL.pullback p).tensor ((hB.pullback g).pullback q))
          (section_ p q f g w L s))) ↔
    (Mono (globalSectionHom _ (pullGlobal p _ s)) ∧
      RelativeEffectiveCartier q
        (lineSectionZeroIdeal ((hL.tensor (hB.pullback f)).pullback p) (pullGlobal p _ s))) := by
  rw [mono_iff, sectionIso_zeroIdeal p q f g w L hL hB s]

end FLT.Mazur.TwistedSectionPullbackMonicity
