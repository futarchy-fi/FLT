/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenPairPrincipalRestriction

/-!
# Full relation lifts from compatibility on the usable open

A compatible boundary lift on a stable open extends to the unchanged affine
target after a power of an original invariant scalar. Compatibility is tested
only where both relation endpoints lie in the usable open. Clearing powers
then proves the equation on the entire original relation, including its
residual points. No global factorization through the usable open is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G]
  {X Y : Scheme} [IsAffine X] [IsAffine Y]
  (ρ : G →* Aut X) (O : X.Opens) (hO : ∀ g, (ρ g).hom ⁻¹ᵁ O = O)
  (r : invariantCoordinates ρ) (hr : X.basicOpen r.val ≤ O) (i : Y ⟶ X)
  {ι : Type} [Finite ι] {Z : ι → Scheme} [∀ a, IsAffine (Z a)]
  (F H : ∀ a, Z a ⟶ X) (hs : ∀ a, (F a).appTop r.val = (H a).appTop r.val)

include hs in
/-- Open-pair compatibility constructs a numerator satisfying every full original equation. -/
theorem pairOpen_principal_relation_lift_numerator
    (v : invariantCoordinates (restrictedAction ρ O hO)) (t : Γ(Y, ⊤))
    (hb : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop t)
    (he : ∀ a, (pairOpenFirst O (F a) (H a)).appTop v.val =
      (pairOpenSecond O (F a) (H a)).appTop v.val) :
    ∃ (n : ℕ) (w : invariantCoordinates ρ),
      i.appTop w.val = (i.appTop r.val) ^ n * t ∧
      (∀ a, (F a).appTop w.val = (H a).appTop w.val) ∧
      (X.basicOpen r.val).ι.appTop w.val =
        ((X.basicOpen r.val).ι.appTop r.val) ^ n * (X.homOfLE hr).appTop v.val := by
  apply principal_invariant_relation_lift_numerator i ρ r F H hs
    (openPrincipalInvariantMap ρ O hO r hr v) t
  · rw [openPrincipalInvariantMap_val]
    change (principalPullbackMap i r.val ≫ X.homOfLE hr).appTop v.val = _
    rw [openPrincipalBoundary_square, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hb]
    change (Y.homOfLE (openPrincipalBoundary_le ρ O r hr i) ≫ (i ⁻¹ᵁ O).ι).appTop t = _
    rw [Scheme.homOfLE_ι]
  · exact fun a ↦ openPrincipalInvariantMap_pairOpen ρ O hO r hr (F a) (H a) (hs a) v (he a)

include hr hs in
/-- A boundary-zero correction solves every full equation, including the residual relation. -/
theorem pairOpen_principal_relation_correction
    (v : invariantCoordinates (restrictedAction ρ O hO)) (u : invariantCoordinates ρ)
    (hb : (i ∣_ O).appTop v.val = (i ⁻¹ᵁ O).ι.appTop (i.appTop u.val))
    (he : ∀ a, (pairOpenFirst O (F a) (H a)).appTop v.val =
      (pairOpenSecond O (F a) (H a)).appTop v.val) :
    ∃ (n : ℕ) (w : invariantCoordinates ρ), i.appTop w.val = 0 ∧
      ∀ a, (F a).appTop w.val - (H a).appTop w.val =
        (F a).appTop r.val ^ n * ((F a).appTop u.val - (H a).appTop u.val) := by
  obtain ⟨n, w, hw, hf, _⟩ := pairOpen_principal_relation_lift_numerator
    ρ O hO r hr i F H hs v (i.appTop u.val) hb he
  refine ⟨n, r ^ n * u - w, ?_, ?_⟩
  · change i.appTop (r.val ^ n * u.val - w.val) = 0
    simp only [map_sub, map_mul, map_pow, hw, sub_self]
  · intro a
    change (F a).appTop (r.val ^ n * u.val - w.val) -
      (H a).appTop (r.val ^ n * u.val - w.val) = _
    simp only [map_sub, map_mul, map_pow, ← hs a, hf a]
    ring

end FLT.Mazur.SchemeFiniteGroupQuotient
