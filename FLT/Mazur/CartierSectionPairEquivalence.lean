/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSectionDivisorCorrespondence

/-!
# Effective Cartier ideals and regular section pairs

An effective Cartier ideal is equivalent to an isomorphism class of an
actual line sheaf with a regular section. Both maps use the full ideals and
actual sheaf morphisms constructed by evaluation and canonical biduality.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

/-- An actual line sheaf and a section whose structure-to-line map is injective. -/
structure RegularLineSection (X : Scheme.{0}) where
  /-- The underlying actual module sheaf. -/
  line : X.Modules
  /-- Local rank one of the underlying sheaf. -/
  isLine : LocallyFreeRankOne line
  /-- The chosen global section. -/
  value : Γ(line, ⊤)
  /-- Injectivity of the section multiplication map. -/
  regular : Mono (globalSectionHom line value)

variable {X : Scheme.{0}}

/-- Equivalence is by an actual line isomorphism preserving the original section. -/
def regularLineSectionSetoid (X : Scheme.{0}) : Setoid (RegularLineSection X) where
  r a b := ∃ e : a.line ≅ b.line, e.hom.app ⊤ a.value = b.value
  iseqv :=
    { refl := fun a ↦ ⟨Iso.refl a.line, rfl⟩
      symm := by
        rintro a b ⟨e, he⟩
        refine ⟨e.symm, ?_⟩
        rw [← he]
        exact congrArg (fun f ↦ f.app ⊤ a.value) e.hom_inv_id
      trans := by
        rintro a b c ⟨e, he⟩ ⟨f, hf⟩
        refine ⟨e ≪≫ f, ?_⟩
        change f.hom.app ⊤ (e.hom.app ⊤ a.value) = c.value
        rw [he, hf] }

/-- The full effective Cartier zero ideal of a regular section pair. -/
def RegularLineSection.zeroDivisor (a : RegularLineSection X) :
    {I : X.IdealSheafData // EffectiveCartier I} := by
  have := a.regular
  exact ⟨lineSectionZeroIdeal a.isLine a.value,
    lineSectionZeroIdeal_effectiveCartier a.isLine a.value⟩

/-- A Cartier ideal has its actual positive line and canonical regular section. -/
def cartierRegularLineSection (D : {I : X.IdealSheafData // EffectiveCartier I}) :
    RegularLineSection X where
  line := divisorLineBundle D.1 D.2
  isLine := D.2.divisorLineBundle_locallyFreeRankOne
  value := divisorSection D.2 ⊤
  regular := by
    rw [globalSectionHom_divisorSection]
    infer_instance

/-- The canonical pair recovers the original full Cartier ideal. -/
lemma cartierRegularLineSection_zeroDivisor
    (D : {I : X.IdealSheafData // EffectiveCartier I}) :
    (cartierRegularLineSection D).zeroDivisor = D := by
  apply Subtype.ext
  exact lineSectionZeroIdeal_divisorSection D.1 D.2

/-- Equal zero divisors are exactly equivalence of actual regular section pairs. -/
lemma RegularLineSection.zeroDivisor_eq_iff (a b : RegularLineSection X) :
    a.zeroDivisor = b.zeroDivisor ↔ (regularLineSectionSetoid X).r a b := by
  have := a.regular
  have := b.regular
  rw [Subtype.ext_iff]
  exact lineSectionZeroIdeal_eq_iff_iso a.isLine b.isLine a.value b.value

/-- Cartier ideals are in bijection with isomorphism classes of regular section pairs. -/
def cartierSectionPairEquiv (X : Scheme.{0}) :
    Quotient (regularLineSectionSetoid X) ≃ {I : X.IdealSheafData // EffectiveCartier I} where
  toFun := Quotient.lift RegularLineSection.zeroDivisor fun a b h ↦
    (a.zeroDivisor_eq_iff b).mpr h
  invFun D := Quotient.mk _ (cartierRegularLineSection D)
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h a =>
      apply Quotient.sound
      apply (RegularLineSection.zeroDivisor_eq_iff _ _).mp
      exact cartierRegularLineSection_zeroDivisor a.zeroDivisor
  right_inv := cartierRegularLineSection_zeroDivisor

/-- The forward equivalence is precisely the evaluation-image construction. -/
lemma cartierSectionPairEquiv_mk (a : RegularLineSection X) :
    cartierSectionPairEquiv X (Quotient.mk _ a) = a.zeroDivisor := rfl

/-- The inverse equivalence is precisely the canonical Cartier section pair. -/
lemma cartierSectionPairEquiv_symm_apply
    (D : {I : X.IdealSheafData // EffectiveCartier I}) :
    (cartierSectionPairEquiv X).symm D = Quotient.mk _ (cartierRegularLineSection D) := rfl

end FLT.Mazur.FCurve
