/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.SplitPairEqualizer

/-!
# Saturated neighborhoods for two augmented affine branches

Principal neighborhoods of the two marked points give a matching pair with
value one. This gives local descent to arbitrary scheme targets, including for
localized branch rings rather than full affine lines.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
namespace FLT.Mazur.SplitPairEqualizer
set_option backward.isDefEq.respectTransparency false
universe u
variable {K C D : Type u} [Field K] [CommRing C] [CommRing D]
  (f : C →+* K) (g : D →+* K) (l : K →+* C) (r : K →+* D)
  (hl : f.comp l = RingHom.id K) (hr : g.comp r = RingHom.id K)

include hl hr in
/-- A saturated principal neighborhood inside any open containing both marked points. -/
theorem principal_pair (U : Opens (PrimeSpectrum (C × D)))
    (h₁ : PrimeSpectrum.comap (leftEval f (D := D)) ⊥ ∈ U)
    (h₂ : PrimeSpectrum.comap (rightEval g (C := C)) ⊥ ∈ U) :
    ∃ s : E f g, leftEval f s.val = 1 ∧ PrimeSpectrum.basicOpen s.val ≤ U := by
  obtain ⟨_, ⟨p, rfl⟩, hp, hpU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h₁ U.isOpen
  obtain ⟨_, ⟨q, rfl⟩, hq, hqU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open h₂ U.isOpen
  have hp0 : f p.1 ≠ 0 := by
    change f p.1 ∉ (⊥ : Ideal K) at hp
    simpa only [Ideal.mem_bot] using hp
  have hq0 : g q.2 ≠ 0 := by
    change g q.2 ∉ (⊥ : Ideal K) at hq
    simpa only [Ideal.mem_bot] using hq
  let a := l (f p.1)⁻¹ * p.1
  let b := r (g q.2)⁻¹ * q.2
  have ha : f a = 1 := by
    rw [map_mul, show f (l (f p.1)⁻¹) = (f p.1)⁻¹ from RingHom.congr_fun hl _]
    exact inv_mul_cancel₀ hp0
  have hb : g b = 1 := by
    rw [map_mul, show g (r (g q.2)⁻¹) = (g q.2)⁻¹ from RingHom.congr_fun hr _]
    exact inv_mul_cancel₀ hq0
  refine ⟨⟨(a, b), ha.trans hb.symm⟩, ha, ?_⟩
  apply RelativePinchingLocalDescent.prod_basicOpen_le
  · intro z hz
    apply hpU
    change p.1 ∉ z.asIdeal
    exact (PrimeSpectrum.basicOpen_mul_le_right _ _) hz
  · intro z hz
    apply hqU
    change q.2 ∉ z.asIdeal
    exact (PrimeSpectrum.basicOpen_mul_le_right _ _) hz

include hl hr in
/-- Every compatible normalization map descends near every prime of the marked field. -/
theorem exists_local_desc {Y : Scheme.{u}} (h : Spec (.of (C × D)) ⟶ Y)
    (w : Spec.map (CommRingCat.ofHom (leftEval f (D := D))) ≫ h =
      Spec.map (CommRingCat.ofHom (rightEval g (C := C))) ≫ h) (x : PrimeSpectrum K) :
    ∃ (s : E f g)
      (d : Spec (.of (RingEqualizerLocalization.E
        (leftEval f (D := D)) (rightEval g (C := C)) s)) ⟶ Y),
      leftEval f s.val ∉ x.asIdeal ∧
        RingEqualizerLocalDescent.branch
          (leftEval f (D := D)) (rightEval g (C := C)) s ≫ d =
          RingEqualizerLocalDescent.branchOpen
            (leftEval f (D := D)) (rightEval g (C := C)) s ≫ h := by
  let o₁ := PrimeSpectrum.comap (leftEval f (D := D)) (⊥ : PrimeSpectrum K)
  let o₂ := PrimeSpectrum.comap (rightEval g (C := C)) (⊥ : PrimeSpectrum K)
  have ho : h o₁ = h o₂ := congrArg (fun k ↦ k (⊥ : PrimeSpectrum K)) w
  obtain ⟨U, hU, hoU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := h o₁) (by trivial)
  obtain ⟨s, hs, hsU⟩ := principal_pair f g l r hl hr (h ⁻¹ᵁ U) hoU
    (by change h o₂ ∈ U; rwa [← ho])
  obtain ⟨d, hd⟩ := RingEqualizerLocalDescent.desc_on_open
    (leftEval f (D := D)) (rightEval g (C := C)) s h w U hU hsU
  exact ⟨s, d, by rw [hs]; exact x.isPrime.one_notMem, hd⟩

end FLT.Mazur.SplitPairEqualizer
