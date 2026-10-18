/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeInvariantPrincipalBoundaryNumerator

/-!
# Clearing exact equations on principal relation tests

Two original maps agreeing on the chosen scalar restrict to the same principal
test scheme. Agreement there kills their original coefficient difference by a
power of that scalar. This detects scheme equations, including nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme} (f g : Y ⟶ X) (r : Γ(X, ⊤))
  (hr : f.appTop r = g.appTop r)

/-- Restrict the second endpoint to the principal domain chosen by the first endpoint. -/
def principalPairSecond :
    (Y.basicOpen (f.appTop r)).toScheme ⟶ (X.basicOpen r).toScheme :=
  g.resLE _ _ (by rw [Scheme.preimage_basicOpen_top, hr])

/-- The second restricted endpoint retains its original map. -/
@[reassoc] theorem principalPairSecond_inclusion :
    principalPairSecond f g r hr ≫ (X.basicOpen r).ι =
      (Y.basicOpen (f.appTop r)).ι ≫ g := Scheme.Hom.resLE_comp_ι _ _

/-- The second endpoint acts on a numerator by the original pullback and restriction. -/
theorem principalPairSecond_appTop (a : Γ(X, ⊤)) :
    (principalPairSecond f g r hr).appTop ((X.basicOpen r).ι.appTop a) =
      (Y.basicOpen (f.appTop r)).ι.appTop (g.appTop a) := by
  change (principalPairSecond f g r hr ≫ (X.basicOpen r).ι).appTop a =
    ((Y.basicOpen (f.appTop r)).ι ≫ g).appTop a
  rw [principalPairSecond_inclusion]

variable [IsAffine Y]

/-- A numerator of a compatible principal section has a power-torsion original error. -/
theorem principal_pair_numerator_power (v : Γ((X.basicOpen r).toScheme, ⊤))
    (w : Γ(X, ⊤)) (n : ℕ)
    (hw : (X.basicOpen r).ι.appTop w = ((X.basicOpen r).ι.appTop r) ^ n * v)
    (hv : (principalPullbackMap f r).appTop v =
      (principalPairSecond f g r hr).appTop v) :
    ∃ k : ℕ, (f.appTop r) ^ k * (f.appTop w - g.appTop w) = 0 := by
  have he : (Y.basicOpen (f.appTop r)).ι.appTop (f.appTop w) =
      (Y.basicOpen (f.appTop r)).ι.appTop (g.appTop w) := by
    rw [← principalPullbackMap_appTop, ← principalPairSecond_appTop f g r hr, hw]
    simp only [map_mul, map_pow, principalPullbackMap_appTop,
      principalPairSecond_appTop, hr, hv]
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (f.appTop r) he
  exact ⟨k, by rw [mul_sub, hk, sub_self]⟩

end FLT.Mazur.SchemeFiniteGroupQuotient
