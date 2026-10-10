/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelSectionQuotient
public import FLT.Mazur.CartierAbelTwistBaseChange

/-!
# The relative Cartier Abel fiber comparison under base change

The twisted-section quotient equivalence restricts to relative divisors.
Direct geometric section pullback descends to the quotient, and the
equivalence commutes with arbitrary test-base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve
variable {X S T : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
variable (hL : LocallyFreeRankOne L)

/-- Relative sections use the same actual section-preserving sheaf isomorphisms. -/
def relativeSectionSetoid : Setoid (RelativeSection f L hL) :=
  (twistedSectionSetoid f L).comap Subtype.val

/-- The relative divisor map detects exactly the actual section-isomorphism relation. -/
theorem relativeSectionToFiber_eq_iff (s t : RelativeSection f L hL) :
    relativeSectionToFiber f L hL s = relativeSectionToFiber f L hL t ↔
      (relativeSectionSetoid f L hL).r s t := by
  have h : relativeSectionToFiber f L hL s = relativeSectionToFiber f L hL t ↔
      TwistedSection.toFiber f L hL s.val = TwistedSection.toFiber f L hL t.val :=
    ⟨fun h ↦ congrArg Subtype.val h, fun h ↦ Subtype.ext h⟩
  exact h.trans (twistedSection_toFiber_eq_iff f L hL s.val t.val)

/-- The relative Abel map on twisted-section isomorphism classes. -/
def relativeQuotientToFiber : Quotient (relativeSectionSetoid f L hL) → RelativeFiber f L hL :=
  Quotient.lift (relativeSectionToFiber f L hL)
    (fun s t h ↦ (relativeSectionToFiber_eq_iff f L hL s t).mpr h)

/-- Full relative Cartier ideals distinguish the section classes. -/
theorem relativeQuotientToFiber_injective :
    Function.Injective (relativeQuotientToFiber f L hL) := by
  intro s t
  induction s using Quotient.inductionOn with | h s =>
    induction t using Quotient.inductionOn with | h t =>
      intro h
      exact Quotient.sound ((relativeSectionToFiber_eq_iff f L hL s t).mp h)

/-- Recovery of a relative divisor retains flatness of its actual zero ideal. -/
theorem relativeQuotientToFiber_surjective :
    Function.Surjective (relativeQuotientToFiber f L hL) := by
  intro D
  obtain ⟨s, hs⟩ := twistedSection_toFiber_surjective f L hL D.val
  have hflat : Flat ((lineSectionZeroIdeal (twist_rankOne f L hL s.baseLine)
      s.section_).subschemeι ≫ f) := by
    change Flat ((TwistedSection.toFiber f L hL s).val.val.subschemeι ≫ f)
    rw [hs]
    exact D.property
  exact ⟨Quotient.mk _ ⟨s, hflat⟩, Subtype.ext hs⟩

/-- Actual relative Abel fibers are exactly relative twisted-section classes. -/
def relativeTwistedSectionEquiv :
    Quotient (relativeSectionSetoid f L hL) ≃ RelativeFiber f L hL :=
  Equiv.ofBijective (relativeQuotientToFiber f L hL)
    ⟨relativeQuotientToFiber_injective f L hL, relativeQuotientToFiber_surjective f L hL⟩

variable (g : T ⟶ S)

/-- Direct sheaf pullback respects section isomorphism classes. -/
theorem relativeSectionBaseChange_respects (s t : RelativeSection f L hL)
    (h : (relativeSectionSetoid f L hL).r s t) :
    (relativeSectionSetoid (Limits.pullback.snd f g) _
      (hL.pullback (Limits.pullback.fst f g))).r
        (relativeSectionBaseChange f g L hL s) (relativeSectionBaseChange f g L hL t) := by
  apply (relativeSectionToFiber_eq_iff _ _ _ _ _).mp
  rw [relativeSectionToFiber_baseChange, relativeSectionToFiber_baseChange,
    (relativeSectionToFiber_eq_iff f L hL s t).mpr h]

/-- Base change of section classes is induced by pulling their actual sheaves and sections. -/
def relativeQuotientBaseChange : Quotient (relativeSectionSetoid f L hL) →
    Quotient (relativeSectionSetoid (Limits.pullback.snd f g) _
      (hL.pullback (Limits.pullback.fst f g))) :=
  Quotient.map (relativeSectionBaseChange f g L hL)
    (relativeSectionBaseChange_respects f L hL g)

/-- The Abel-fiber equivalence commutes with arbitrary geometric test-base change. -/
theorem relativeTwistedSectionEquiv_baseChange (s : Quotient (relativeSectionSetoid f L hL)) :
    relativeTwistedSectionEquiv _ _ _ (relativeQuotientBaseChange f L hL g s) =
      fiberBaseChange f g L hL (relativeTwistedSectionEquiv f L hL s) := by
  induction s using Quotient.inductionOn with | h s =>
    exact relativeSectionToFiber_baseChange f g L hL s

end FLT.Mazur.CartierAbel
