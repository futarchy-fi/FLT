/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Residue-field detection of functions on reduced schemes

A function on a reduced scheme vanishes if it vanishes at every residue-field
point. The proof uses the empty basic open criterion, and preserves the actual
maps on global functions induced by those scheme points.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeReducedSectionDetection
variable {X : Scheme.{u}} [IsReduced X]
/-- Vanishing after pullback to every residue-field point detects the zero section. -/
lemma eq_zero_of_residue_pullback (r : Γ(X, ⊤))
    (h : ∀ x : X, (X.fromSpecResidueField x).appTop r = 0) : r = 0 := by
  apply eq_zero_of_basicOpen_eq_bot r
  apply eq_bot_iff.mpr
  intro x hx
  have hx' : (X.fromSpecResidueField x) (default : Spec (X.residueField x)) ∈
      X.basicOpen r := by simpa using hx
  change (default : Spec (X.residueField x)) ∈
    (X.fromSpecResidueField x) ⁻¹ᵁ X.basicOpen r at hx'
  rw [Scheme.preimage_basicOpen_top, h x, Scheme.basicOpen_zero] at hx'
  exact hx'
/-- Equality of sections is detected by the actual residue-field pullbacks. -/
lemma eq_of_residue_pullback (r t : Γ(X, ⊤))
    (h : ∀ x : X, (X.fromSpecResidueField x).appTop r =
      (X.fromSpecResidueField x).appTop t) : r = t := by
  apply sub_eq_zero.mp
  apply eq_zero_of_residue_pullback
  intro x
  rw [map_sub, h x, sub_self]

/-- Ring maps into reduced-scheme functions agree if every residue pullback agrees. -/
lemma hom_ext {R : CommRingCat.{u}} (a b : R ⟶ Γ(X, ⊤))
    (h : ∀ x : X, a ≫ (X.fromSpecResidueField x).appTop =
      b ≫ (X.fromSpecResidueField x).appTop) : a = b := by
  ext r
  apply eq_of_residue_pullback
  intro x
  exact ConcreteCategory.congr_hom (h x) r

end FLT.Mazur.SchemeReducedSectionDetection
