/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelTwistedSections

/-!
# The Abel fiber as actual twisted section isomorphism classes

The relation is an isomorphism of actual coefficient sheaves carrying one
section to the other. The quotient is equivalent to the full Cartier fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.CartierAbel
open FCurve
variable {X S : Scheme.{0}} (f : X ⟶ S) (L : X.Modules)
variable (hL : LocallyFreeRankOne L)

/-- Full zero ideals classify twisted sections up to section-preserving sheaf isomorphism. -/
theorem twistedSection_toFiber_eq_iff (s t : TwistedSection f L) :
    TwistedSection.toFiber f L hL s = TwistedSection.toFiber f L hL t ↔
      ∃ e : twist f L s.baseLine ≅ twist f L t.baseLine,
        e.hom.app ⊤ s.section_ = t.section_ := by
  have h : TwistedSection.toFiber f L hL s = TwistedSection.toFiber f L hL t ↔
      lineSectionZeroIdeal (twist_rankOne f L hL s.baseLine) s.section_ =
        lineSectionZeroIdeal (twist_rankOne f L hL t.baseLine) t.section_ :=
    ⟨fun h ↦ congrArg (fun D ↦ D.val.val) h, fun h ↦ Subtype.ext (Subtype.ext h)⟩
  exact h.trans (lineSectionZeroIdeal_eq_iff_iso (twist_rankOne f L hL s.baseLine)
    (twist_rankOne f L hL t.baseLine) s.section_ t.section_)

/-- The relation retains the actual sheaf comparison and its effect on the original section. -/
def twistedSectionSetoid : Setoid (TwistedSection f L) where
  r s t := ∃ e : twist f L s.baseLine ≅ twist f L t.baseLine,
    e.hom.app ⊤ s.section_ = t.section_
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      exact ⟨Iso.refl _, rfl⟩
    · rintro s t ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      rw [← he]
      exact congrArg (fun a ↦ a.app ⊤ s.section_) e.hom_inv_id
    · rintro s t v ⟨e, he⟩ ⟨d, hd⟩
      refine ⟨e ≪≫ d, ?_⟩
      change d.hom.app ⊤ (e.hom.app ⊤ s.section_) = v.section_
      rw [he, hd]

/-- The zero-divisor map on actual section-isomorphism classes. -/
def quotientToFiber : Quotient (twistedSectionSetoid f L) → Fiber f L hL :=
  Quotient.lift (TwistedSection.toFiber f L hL)
    (fun s t h ↦ (twistedSection_toFiber_eq_iff f L hL s t).mpr h)

/-- Equality in the Cartier fiber detects precisely the quotient relation. -/
theorem quotientToFiber_injective : Function.Injective (quotientToFiber f L hL) := by
  intro s t
  induction s using Quotient.inductionOn with | h s =>
    induction t using Quotient.inductionOn with | h t =>
      intro h
      exact Quotient.sound ((twistedSection_toFiber_eq_iff f L hL s t).mp h)

/-- The canonical divisor section supplies every quotient fiber point. -/
theorem quotientToFiber_surjective : Function.Surjective (quotientToFiber f L hL) := by
  intro D
  obtain ⟨s, hs⟩ := twistedSection_toFiber_surjective f L hL D
  exact ⟨Quotient.mk _ s, hs⟩

/-- The actual Abel fiber is exactly the twisted regular-section quotient. -/
def twistedSectionEquiv : Quotient (twistedSectionSetoid f L) ≃ Fiber f L hL :=
  Equiv.ofBijective (quotientToFiber f L hL)
    ⟨quotientToFiber_injective f L hL, quotientToFiber_surjective f L hL⟩

/-- The equivalence takes each original section to its full zero ideal. -/
lemma twistedSectionEquiv_mk (s : TwistedSection f L) :
    twistedSectionEquiv f L hL (Quotient.mk _ s) = TwistedSection.toFiber f L hL s := rfl

end FLT.Mazur.CartierAbel
