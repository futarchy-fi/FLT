/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierAbelFiber

/-!
# Regular sections with retained test-base twists

Every base line is allowed. Taking the full zero ideal lands in the actual
Abel fiber, and the canonical divisor section proves surjectivity.
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

/-- The actual coefficient line after a test-base twist. -/
def twist (B : SchemePicard.LineBundle S) : X.Modules :=
  ModuleSheafTensor.tensor L ((pullback f).obj B.val)

include hL in
/-- Tensoring with any pulled base line retains rank one. -/
theorem twist_rankOne (B : SchemePicard.LineBundle S) :
    LocallyFreeRankOne (twist f L B) := hL.tensor (B.property.pullback f)

/-- A base line together with a regular section of the corresponding actual twist. -/
structure TwistedSection where
  /-- The twisting line on the original test base. -/
  baseLine : SchemePicard.LineBundle S
  /-- The section of the actual tensor product on the total space. -/
  section_ : Γ(twist f L baseLine, ⊤)
  /-- The section cuts out an effective Cartier divisor. -/
  regular : Mono (globalSectionHom (twist f L baseLine) section_)

attribute [instance] TwistedSection.regular

/-- Taking the zero divisor of a twisted section gives the original relative class. -/
def TwistedSection.toFiber (s : TwistedSection f L) : Fiber f L hL :=
  ⟨⟨lineSectionZeroIdeal (twist_rankOne f L hL s.baseLine) s.section_,
    lineSectionZeroIdeal_effectiveCartier (twist_rankOne f L hL s.baseLine) s.section_⟩, by
    rw [abel_zero]
    exact SchemePicard.relativeClass_base_twist f (SchemePicard.mk L hL)
      (SchemePicard.mk s.baseLine.val s.baseLine.property)⟩

/-- Transport of the canonical divisor section is regular on the actual twisted sheaf. -/
def sectionOfDivisor (D : Divisor X) (B : SchemePicard.LineBundle S)
    (e : divisorLineBundle D.val D.property ≅ twist f L B) : TwistedSection f L where
  baseLine := B
  section_ := e.hom.app ⊤ (divisorSection D.property ⊤)
  regular := by
    rw [← globalSectionHom_naturality, globalSectionHom_divisorSection]
    infer_instance

/-- The transported section retains the full ideal of the input divisor. -/
lemma sectionOfDivisor_zero (D : Divisor X) (B : SchemePicard.LineBundle S)
    (e : divisorLineBundle D.val D.property ≅ twist f L B) :
    (TwistedSection.toFiber f L hL (sectionOfDivisor f L D B e)).val = D := by
  apply Subtype.ext
  exact (lineSectionZeroIdeal_eq_of_iso D.property.divisorLineBundle_locallyFreeRankOne
    (twist_rankOne f L hL B) e (divisorSection D.property ⊤)
    (e.hom.app ⊤ (divisorSection D.property ⊤)) rfl).symm.trans
      (lineSectionZeroIdeal_divisorSection D.val D.property)

/-- Every point of the actual Abel fiber comes from a regular section with a base twist. -/
theorem twistedSection_toFiber_surjective :
    Function.Surjective (TwistedSection.toFiber f L hL) := by
  intro D
  obtain ⟨B, ⟨e⟩⟩ := (mem_fiber_iff f hL D.val).mp D.property
  refine ⟨sectionOfDivisor f L D.val B e, Subtype.ext ?_⟩
  exact sectionOfDivisor_zero f L hL D.val B e

end FLT.Mazur.CartierAbel
