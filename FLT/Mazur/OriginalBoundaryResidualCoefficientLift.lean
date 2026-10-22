/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryResidualIdeal

/-!
# Original invariant lifts of residual coefficient corrections

A shared original residual scalar has a power lifting any invariant boundary
section. Full coefficient tests on which it agrees with a prescribed scalar
therefore acquire one original invariant numerator. This does not assert
that the coefficient tests detect the whole original boundary section.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A}
  [IsSeparated p] [Etale p] [QuasiCompact p] [IsAffine A]
  (J : A.IdealSheafData) (e : CategoryTheory.EquivalenceRelation p q)
  (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local notation "R" => compatibleFunctions p q
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J
local notation "ρ" => J.subschemeι.appTop.hom.comp (Subring.subtype R)

include e hf in
/-- One shared residual correction constructs an original invariant numerator on all tests. -/
theorem originalBoundary_residual_coefficient_lift {ι : Type*}
    {B : ι → Type*} [∀ i, CommRing (B i)] (φ : ∀ i, Γ(J.subscheme, ⊤) →+* B i)
    (a : R) (h : ∃ b ∈ H, ∀ i, φ i (ρ a) = φ i (ρ b)) :
    ∃ (k : ℕ) (u : R), ∀ i, φ i (ρ u) = φ i (ρ (a ^ k) * t.val) := by
  obtain ⟨b, hb, hab⟩ := h
  obtain ⟨k, hk⟩ := originalBoundaryResidualIdeal_le_lift_radical J e hJ f hf t hb
  obtain ⟨u, hu⟩ := hk
  refine ⟨k, u, fun i ↦ ?_⟩
  change φ i (J.subschemeι.appTop u.val) = _
  rw [hu]
  change φ i (ρ (b ^ k) * t.val) = φ i (ρ (a ^ k) * t.val)
  simp only [map_mul, map_pow, hab i]

include e hf in
/-- The same construction handles a prescribed scalar power without cancelling it. -/
theorem originalBoundary_residual_power_coefficient_lift {ι : Type*}
    {B : ι → Type*} [∀ i, CommRing (B i)] (φ : ∀ i, Γ(J.subscheme, ⊤) →+* B i)
    (a : R) (d : ℕ) (h : ∃ b ∈ H, ∀ i, φ i (ρ (a ^ d)) = φ i (ρ b)) :
    ∃ (k : ℕ) (u : R), ∀ i, φ i (ρ u) = φ i (ρ (a ^ (d * k)) * t.val) := by
  obtain ⟨k, u, hu⟩ := originalBoundary_residual_coefficient_lift J e hJ f hf t φ (a ^ d) h
  exact ⟨k, u, fun i ↦ by simpa only [pow_mul] using hu i⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
