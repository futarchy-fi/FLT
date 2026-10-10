/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilyLineDescent
public import FLT.Mazur.LineTensorLeftCancellation
public import FLT.Mazur.OriginalTwistOrbitRelation

/-!
# Original twisted-section descent on unrestricted test families

The diagonal supplies line-isomorphism descent without an original family
section. Cancelling the fixed line retains the given isomorphism's action
on the original tensor section, and hence its full Cartier zero divisor.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProperFamilyLineDescent
open FCurve CartierAbel ModuleSheafTensor
attribute [local irreducible] tensor
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [Surjective f]
  [GeometricallyConnected f] [GeometricallyReduced f] (h : IsPullback p q f g)
  (L : P.Modules) (hL : LocallyFreeRankOne L)

/-- Recover the original base-line isomorphism from an arbitrary total-space twisted isomorphism. -/
def descendTwistIso {B C : SchemePicard.LineBundle T}
    (e : twist q L B ≅ twist q L C) : B.val ≅ C.val :=
  descendIso h B.property C.property (cancelLeftLineIso hL e)

/-- The descended base-line isomorphism acts by the entire original tensor map. -/
lemma descendTwistIso_hom {B C : SchemePicard.LineBundle T}
    (e : twist q L B ≅ twist q L C) :
    map (𝟙 L) ((pullback q).map (descendTwistIso h L hL e).hom) = e.hom := by
  have hh := congrArg Iso.hom (mapIso_descendIso h
    B.property C.property (cancelLeftLineIso hL e))
  change (pullback q).map (descendTwistIso h L hL e).hom =
    (cancelLeftLineIso hL e).hom at hh
  rw [hh, cancelLeftLineIso_hom]

include h hL in
/-- Total-space twisted-section orbits are precisely original base-line orbits. -/
theorem sectionSetoid_iff_baseIso (s t : TwistedSection q L) :
    (twistedSectionSetoid q L).r s t ↔
      ∃ e : s.baseLine.val ≅ t.baseLine.val,
        (map (𝟙 L) ((pullback q).map e.hom)).app ⊤ s.section_ = t.section_ := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨descendTwistIso h L hL e, ?_⟩
    rw [descendTwistIso_hom]
    exact he
  · rintro ⟨e, he⟩
    exact ⟨congr (Iso.refl L) ((pullback q).mapIso e), he⟩

include h hL in
/-- Actual total-space orbits agree with the original twisting-line relation on every test base. -/
lemma sectionSetoid_iff_originalTwistRelation (s t : TwistedSection q L) :
    (twistedSectionSetoid q L).r s t ↔ originalTwistIsoRelation q L s t := by
  unfold originalTwistIsoRelation
  exact sectionSetoid_iff_baseIso h L hL s t

end FLT.Mazur.ProperFamilyLineDescent
