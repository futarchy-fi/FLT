/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineLocallyFreeSimultaneousTrace
public import FLT.Mazur.AffineClosedSimultaneousLifting
public import FLT.Mazur.AffineFiniteEtaleBoundarySurjectivity

/-!
# Simultaneous full invariant lifts on intersecting closed subschemes

The two restrictions are solved jointly, using agreement on the exact
intersection. All trace charts are constructed from finite etale geometry.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineFiniteEtaleSimultaneousLifting
open SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
variable {D A S : Scheme.{0}} [IsAffine A] [IsAffine S]
  (p q : D ⟶ A) (f : A ⟶ S) (hf : p ≫ f = q ≫ f)
  (e : CategoryTheory.EquivalenceRelation p q) [IsFinite p] [Etale p] [IsSeparated f]
  {D₁ A₁ D₂ A₂ Z : Scheme.{0}} [IsAffine A₁] [IsAffine A₂]
  (p₁ q₁ : D₁ ⟶ A₁) (a₁ : A₁ ⟶ A) (b₁ : D₁ ⟶ D)
  (H₁ : IsPullback b₁ p₁ p a₁) (hq₁ : b₁ ≫ q = q₁ ≫ a₁)
  (p₂ q₂ : D₂ ⟶ A₂) (a₂ : A₂ ⟶ A) (b₂ : D₂ ⟶ D)
  (H₂ : IsPullback b₂ p₂ p a₂) (hq₂ : b₂ ≫ q = q₂ ≫ a₂)
  (j : Z ⟶ A₁) (g : Z ⟶ A₂) (H : IsPullback j g a₁ a₂)
  [IsClosedImmersion a₁] [IsClosedImmersion a₂]

include hf e H in
/-- Compatible full invariants on two closed subschemes lift simultaneously. -/
theorem exists_lift (x : compatibleFunctions p₁ q₁) (y : compatibleFunctions p₂ q₂)
    (hxy : j.appTop x.val = g.appTop y.val) :
    ∃ z : compatibleFunctions p q,
      relationPullback p q p₁ q₁ a₁ b₁ H₁.w hq₁ z = x ∧
      relationPullback p q p₂ q₂ a₂ b₂ H₂.w hq₂ z = y := by
  obtain ⟨c, hx, hy⟩ := AffineClosedSimultaneousLifting.exists_lift a₁ a₂ j g H
    x.val y.val hxy
  let _ : IsAffine D := isAffine_of_isAffineHom p
  let _ : IsFinite p₁ := MorphismProperty.of_isPullback H₁ (inferInstanceAs (IsFinite p))
  let _ : IsFinite p₂ := MorphismProperty.of_isPullback H₂ (inferInstanceAs (IsFinite p))
  let _ : IsAffine D₁ := isAffine_of_isAffineHom p₁
  let _ : IsAffine D₂ := isAffine_of_isAffineHom p₂
  let _ := p.appTop.hom.toAlgebra
  let hfin := p.finite_appTop
  let hp := FCurve.finiteFlat_appTop_projective p
  exact AffineLocallyFreeSimultaneousTrace.exists_invariant_lift p q f hf e
    (FiniteProjectiveAffineNorm.chart p hfin hp)
    (FiniteProjectiveAffineNorm.chart_basis p hfin hp)
    (FiniteProjectiveAffineNorm.chart_cover p hfin hp)
    p₁ q₁ a₁ b₁ H₁ hq₁ p₂ q₂ a₂ b₂ H₂ hq₂ x y c hx hy

end FLT.Mazur.AffineFiniteEtaleSimultaneousLifting
