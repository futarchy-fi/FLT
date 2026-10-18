/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemePrincipalPairRestriction
public import FLT.Mazur.FinitePowerEqualizer

/-!
# Extending principal invariant lifts with all original relation equations

On a fixed affine target, an invariant lift on a specified principal open
extends after a power of its original scalar. One further common power clears
every equation in a finite family of affine relation tests. The same numerator
preserves the exact scaled boundary value and all full relation equations.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] [Finite G] {X Y : Scheme} [IsAffine X] [IsAffine Y]
  (i : Y ⟶ X) (ρ : G →* Aut X) (r : invariantCoordinates ρ)
  {ι : Type} [Finite ι] {Z : ι → Scheme} [∀ a, IsAffine (Z a)]
  (f g : ∀ a, Z a ⟶ X) (hr : ∀ a, (f a).appTop r.val = (g a).appTop r.val)

/-- Principal compatible lifts extend to the unchanged affine target with one scalar power. -/
theorem principal_invariant_relation_lift_numerator
    (v : invariantCoordinates (principalAction ρ r)) (t : Γ(Y, ⊤))
    (hb : (principalPullbackMap i r.val).appTop v.val =
      (Y.basicOpen (i.appTop r.val)).ι.appTop t)
    (he : ∀ a, (principalPullbackMap (f a) r.val).appTop v.val =
      (principalPairSecond (f a) (g a) r.val (hr a)).appTop v.val) :
    ∃ (n : ℕ) (w : invariantCoordinates ρ),
      i.appTop w.val = (i.appTop r.val) ^ n * t ∧
      (∀ a, (f a).appTop w.val = (g a).appTop w.val) ∧
      (X.basicOpen r.val).ι.appTop w.val =
        ((X.basicOpen r.val).ι.appTop r.val) ^ n * v.val := by
  obtain ⟨n, w, hw, hv⟩ := principal_invariant_boundary_lift_numerator i ρ r v t hb
  have hp (a : ι) : ∃ k : ℕ,
      (f a).appTop r.val ^ k * ((f a).appTop w.val - (g a).appTop w.val) = 0 :=
    principal_pair_numerator_power (f a) (g a) r.val (hr a) v.val w.val n hv (he a)
  obtain ⟨k, hk⟩ := FinitePowerEqualizer.exists_compatible_power_mul
    (fun a ↦ (f a).appTop.hom) (fun a ↦ (g a).appTop.hom) r.val w.val hr hp
  refine ⟨k + n, r ^ k * w, ?_, hk, ?_⟩
  · change i.appTop (r.val ^ k * w.val) = _
    simp only [map_mul, map_pow, hw, pow_add, mul_assoc]
  · change (X.basicOpen r.val).ι.appTop (r.val ^ k * w.val) = _
    simp only [map_mul, map_pow, hv, pow_add, mul_assoc]

/-- Independent global lifts receive an exact boundary-zero correction for every equation. -/
theorem principal_invariant_relation_correction
    (v : invariantCoordinates (principalAction ρ r)) (u : invariantCoordinates ρ)
    (hb : (principalPullbackMap i r.val).appTop v.val =
      (Y.basicOpen (i.appTop r.val)).ι.appTop (i.appTop u.val))
    (he : ∀ a, (principalPullbackMap (f a) r.val).appTop v.val =
      (principalPairSecond (f a) (g a) r.val (hr a)).appTop v.val) :
    ∃ (n : ℕ) (w : invariantCoordinates ρ), i.appTop w.val = 0 ∧
      ∀ a, (f a).appTop w.val - (g a).appTop w.val =
        (f a).appTop r.val ^ n * ((f a).appTop u.val - (g a).appTop u.val) := by
  obtain ⟨n, w, hw, hf, _⟩ := principal_invariant_relation_lift_numerator
    i ρ r f g hr v (i.appTop u.val) hb he
  refine ⟨n, r ^ n * u - w, ?_, ?_⟩
  · change i.appTop (r.val ^ n * u.val - w.val) = 0
    simp only [map_sub, map_mul, map_pow, hw, sub_self]
  · intro a
    change (f a).appTop (r.val ^ n * u.val - w.val) -
      (g a).appTop (r.val ^ n * u.val - w.val) = _
    simp only [map_sub, map_mul, map_pow, ← hr a, hf a]
    ring

end FLT.Mazur.SchemeFiniteGroupQuotient
