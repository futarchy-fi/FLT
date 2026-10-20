/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeRelationTraceUnit

/-!
# Simultaneous invariant lifting by full relation traces

A single ambient coefficient with two prescribed invariant restrictions can
be replaced by an invariant coefficient with both restrictions unchanged.
Trace multipliers generate one; no division by a rank is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineLocallyFreeSimultaneousTrace
open SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
open AffineLocallyFreeRelationTrace
set_option backward.isDefEq.respectTransparency false
variable {D A S : Scheme.{0}} [IsAffine D] [IsAffine A] [IsAffine S]
  (p q : D ⟶ A) (f : A ⟶ S) (hf : p ≫ f = q ≫ f)
  (e : CategoryTheory.EquivalenceRelation p q) [IsFinite p] [Etale p] [IsSeparated f]
  {κ : Type} (U : κ → A.affineOpens)
  (hU : ∀ j, AffineOpenNorm.HasBasis p (U j)) (hcover : ⨆ j, (U j).1 = ⊤)
  {D₁ A₁ D₂ A₂ : Scheme.{0}} [IsAffine D₁] [IsAffine A₁]
  [IsAffine D₂] [IsAffine A₂]
  (p₁ q₁ : D₁ ⟶ A₁) (a₁ : A₁ ⟶ A) (b₁ : D₁ ⟶ D)
  (H₁ : IsPullback b₁ p₁ p a₁) (hq₁ : b₁ ≫ q = q₁ ≫ a₁)
  (p₂ q₂ : D₂ ⟶ A₂) (a₂ : A₂ ⟶ A) (b₂ : D₂ ⟶ D)
  (H₂ : IsPullback b₂ p₂ p a₂) (hq₂ : b₂ ≫ q = q₂ ≫ a₂)
local notation "φ₁" => relationPullback p q p₁ q₁ a₁ b₁ H₁.w hq₁
local notation "φ₂" => relationPullback p q p₂ q₂ a₂ b₂ H₂.w hq₂

include hf e hU hcover in
/-- One ambient simultaneous lift gives one full invariant simultaneous lift. -/
theorem exists_invariant_lift (x : compatibleFunctions p₁ q₁)
    (y : compatibleFunctions p₂ q₂) (c : Γ(A, ⊤))
    (hx : a₁.appTop c = x.val) (hy : a₂.appTop c = y.val) :
    ∃ z : compatibleFunctions p q, φ₁ z = x ∧ φ₂ z = y := by
  let φ := (φ₁).prod (φ₂)
  have ht : sectionLiftIdeal φ (x, y) = ⊤ := by
    apply top_unique
    rw [← AffineLocallyFreeRelationTraceUnit.invariantTraceIdeal_eq_top
      p q f hf e U hU hcover]
    apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    refine ⟨invariantTrace p q U hU hcover e (s * c), ?_⟩
    apply Prod.ext
    · exact boundary_weightedTrace p q U hU hcover e p₁ q₁ a₁ b₁ H₁ hq₁ x c hx s
    · exact boundary_weightedTrace p q U hU hcover e p₂ q₂ a₂ b₂ H₂ hq₂ y c hy s
  obtain ⟨z, hz⟩ := (sectionLiftIdeal_eq_top_iff φ (x, y)).mp ht
  exact ⟨z, congrArg Prod.fst hz, congrArg Prod.snd hz⟩

end FLT.Mazur.AffineLocallyFreeSimultaneousTrace
