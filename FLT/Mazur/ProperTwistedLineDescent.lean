/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineIsomorphismDescent
public import FLT.Mazur.LineTensorLeftCancellation
public import FLT.Mazur.CartierAbelSectionQuotient

/-!
# Unpointed descent of the actual twisted-section relation

The diagonal supplies line-isomorphism descent without an original family
section. Cancelling the fixed line retains the given isomorphism's action
on the original tensor section, and hence its full Cartier zero divisor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProperLineIsomorphismDescent
open FCurve CartierAbel ModuleSheafTensor
attribute [local irreducible] tensor
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
  [IsLocallyNoetherian S] [IsProper f] [Flat f] [Surjective f]
  [GeometricallyConnected f] [GeometricallyReduced f] (hL : LocallyFreeRankOne L)

/-- Recover the original base-line isomorphism from an arbitrary total-space twisted isomorphism. -/
def descendTwistIso {B C : SchemePicard.LineBundle S}
    (e : twist f L B ≅ twist f L C) : B.val ≅ C.val :=
  descendIso f B.property C.property (cancelLeftLineIso hL e)

/-- The descended base-line isomorphism acts by the entire original tensor map. -/
lemma descendTwistIso_hom {B C : SchemePicard.LineBundle S}
    (e : twist f L B ≅ twist f L C) :
    map (𝟙 L) ((pullback f).map (descendTwistIso f L hL e).hom) = e.hom := by
  have h := congrArg Iso.hom (mapIso_descendIso f
    B.property C.property (cancelLeftLineIso hL e))
  change (pullback f).map (descendTwistIso f L hL e).hom =
    (cancelLeftLineIso hL e).hom at h
  rw [h, cancelLeftLineIso_hom]

include hL in
/-- Total-space twisted-section orbits are precisely original base-line orbits. -/
theorem sectionSetoid_iff_baseIso (s t : TwistedSection f L) :
    (twistedSectionSetoid f L).r s t ↔
      ∃ e : s.baseLine.val ≅ t.baseLine.val,
        (map (𝟙 L) ((pullback f).map e.hom)).app ⊤ s.section_ = t.section_ := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨descendTwistIso f L hL e, ?_⟩
    rw [descendTwistIso_hom]
    exact he
  · rintro ⟨e, he⟩
    exact ⟨congr (Iso.refl L) ((pullback f).mapIso e), he⟩

end FLT.Mazur.ProperLineIsomorphismDescent
