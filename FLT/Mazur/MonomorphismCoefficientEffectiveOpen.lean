/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismRelativeOpen
public import FLT.Mazur.MonomorphismPrincipalInverseCover
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Original coefficient certificates for effective principal target opens

A target coefficient whose pullback belongs to the ideal of principal
inverse charts constructs an effective principal target neighborhood. A
nonnilpotent coefficient proves nonemptiness even on nonreduced targets.
No integrality, generic flatness, or replacement by a prime stratum is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.MonomorphismRelativeOpen
variable {D K T : Scheme.{u}} (m : D ⟶ K) (q : K ⟶ T)

/-- Ideal membership of a literal pulled-back coefficient retains the entire kernel fiber. -/
theorem basicOpen_le_targetOpen_of_mem_span (s : Finset Γ(K, ⊤))
    (hs : ∀ t ∈ s, ∃ a : (K.basicOpen t).toScheme ⟶ D, a ≫ m = (K.basicOpen t).ι)
    (r : Γ(T, ⊤)) (hr : q.appTop r ∈ Ideal.span (s : Set Γ(K, ⊤))) :
    T.basicOpen r ≤ targetOpen m q := by
  apply SchemeWholeFiberOpen.le_locus
  rw [Scheme.preimage_basicOpen_top]
  intro x hx
  by_contra hbad
  have hz : x ∈ K.zeroLocus (s : Set Γ(K, ⊤)) := by
    apply (K.mem_zeroLocus_iff _ x).mpr
    intro t ht hxt
    obtain ⟨a, ha⟩ := hs t ht
    exact hbad (MonomorphismOpenImage.le_locus m (K.basicOpen t) a ha hxt)
  rw [← K.zeroLocus_span] at hz
  exact (K.mem_zeroLocus_iff _ x).mp hz (q.appTop r) hr hx

/-- A nonnilpotent original coefficient gives a nonempty effective target on nonreduced bases. -/
theorem targetOpen_nonempty_of_coefficient [CompactSpace T] (s : Finset Γ(K, ⊤))
    (hs : ∀ t ∈ s, ∃ a : (K.basicOpen t).toScheme ⟶ D, a ≫ m = (K.basicOpen t).ι)
    (r : Γ(T, ⊤)) (hr : q.appTop r ∈ Ideal.span (s : Set Γ(K, ⊤)))
    (hn : ¬ IsNilpotent r) : (targetOpen m q : Set T).Nonempty := by
  have hne : T.basicOpen r ≠ ⊥ := fun h ↦ hn ((Scheme.isNilpotent_iff_basicOpen_eq_bot r).mpr h)
  obtain ⟨x, hx⟩ := (T.basicOpen r).ne_bot_iff_nonempty.mp hne
  exact ⟨x, basicOpen_le_targetOpen_of_mem_span m q s hs r hr hx⟩

variable [Mono m]

/-- Every full kernel test over the certified principal neighborhood has its original inverse. -/
theorem test_lift_of_coefficient (s : Finset Γ(K, ⊤))
    (hs : ∀ t ∈ s, ∃ a : (K.basicOpen t).toScheme ⟶ D, a ≫ m = (K.basicOpen t).ι)
    (r : Γ(T, ⊤)) (hr : q.appTop r ∈ Ideal.span (s : Set Γ(K, ⊤)))
    {Z : Scheme.{u}} (a : Z ⟶ K) (ha : Set.range (a ≫ q) ⊆ T.basicOpen r) :
    ∃! b : Z ⟶ D, b ≫ m = a :=
  test_lift m q a (ha.trans (basicOpen_le_targetOpen_of_mem_span m q s hs r hr))


omit [Mono m] in
/-- Affine kernel vanishing detects a power of an actual coefficient in the inverse-chart ideal. -/
theorem mem_radical_of_basicOpen_le [IsAffine K] (s : Finset Γ(K, ⊤)) (r : Γ(K, ⊤))
    (h : K.basicOpen r ≤ ⨆ t : s, K.basicOpen t.val) :
    r ∈ (Ideal.span (s : Set Γ(K, ⊤))).radical := by
  have hz : K.zeroLocus (s : Set Γ(K, ⊤)) ⊆ K.zeroLocus {r} := by
    intro x hx
    apply (K.mem_zeroLocus_iff _ x).mpr
    intro t ht hxt
    obtain rfl := Set.mem_singleton_iff.mp ht
    obtain ⟨t, ht⟩ := Opens.mem_iSup.mp (h hxt)
    exact (K.mem_zeroLocus_iff _ x).mp hx t.val t.property ht
  have hi : PrimeSpectrum.zeroLocus (s : Set Γ(K, ⊤)) ⊆ PrimeSpectrum.zeroLocus {r} := by
    rw [← K.toSpecΓ_image_zeroLocus, ← K.toSpecΓ_image_zeroLocus]
    exact Set.image_mono hz
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.zeroLocus_span]
  apply (PrimeSpectrum.mem_vanishingIdeal _ _).mpr
  intro z hz
  exact (PrimeSpectrum.mem_zeroLocus _ _).mp (hi hz) (Set.mem_singleton r)

/-- Nonempty effectivity over affine Noetherian kernels is a finite coefficient certificate.
The target is allowed to be nonreduced, and the witness is required to be nonnilpotent. -/
theorem targetOpen_nonempty_iff_coefficient [IsAffine K] [NoetherianSpace K] [IsAffine T] :
    (targetOpen m q : Set T).Nonempty ↔
      ∃ (s : Finset Γ(K, ⊤)) (r : Γ(T, ⊤)),
        (∀ t ∈ s, ∃ a : (K.basicOpen t).toScheme ⟶ D, a ≫ m = (K.basicOpen t).ι) ∧
        q.appTop r ∈ Ideal.span (s : Set Γ(K, ⊤)) ∧ ¬ IsNilpotent r := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨r, hr, hxr⟩ := (isAffineOpen_top T).exists_basicOpen_le ⟨x, hx⟩ (by trivial)
    have hn : ¬ IsNilpotent r := by
      intro hn
      rw [(Scheme.isNilpotent_iff_basicOpen_eq_bot r).mp hn] at hxr
      exact hxr
    obtain ⟨s, he, hs⟩ := MonomorphismOpenImage.exists_principal_inverse_cover m
    have hp : K.basicOpen (q.appTop r) ≤ ⨆ t : s, K.basicOpen t.val := by
      rw [he, ← Scheme.preimage_basicOpen_top]
      exact (q.preimage_mono hr).trans (SchemeWholeFiberOpen.preimage_le q _)
    obtain ⟨n, hn'⟩ := (Ideal.mem_radical_iff).mp (mem_radical_of_basicOpen_le s _ hp)
    refine ⟨s, r ^ n, hs, ?_, fun h ↦ hn h.of_pow⟩
    simpa only [map_pow] using hn'
  · rintro ⟨s, r, hs, hr, hn⟩
    exact targetOpen_nonempty_of_coefficient m q s hs r hr hn

end FLT.Mazur.MonomorphismRelativeOpen
