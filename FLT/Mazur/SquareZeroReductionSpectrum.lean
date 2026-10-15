/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SquareZeroReductionKernel
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Spectra of rings with a common square-zero reduction

Surjective maps with square-zero kernels induce homeomorphisms. A map
compatible with two such reductions therefore induces a homeomorphism as
well, without requiring that map to be an isomorphism of rings.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.SquareZeroReductionKernel
variable {A B N : Type*} [CommRing A] [CommRing B] [CommRing N]

/-- A surjective reduction with square-zero kernel induces the actual spectral homeomorphism. -/
theorem comap_isHomeomorph (r : A →+* N) (hr : Function.Surjective r)
    (hsq : ∀ z, r z = 0 → z * z = 0) : IsHomeomorph (PrimeSpectrum.comap r) := by
  apply PrimeSpectrum.isHomeomorph_comap r
  · intro z
    obtain ⟨a, ha⟩ := hr z
    exact ⟨1, Nat.zero_lt_one, a, ha.trans (pow_one z).symm⟩
  · intro z hz
    exact ⟨2, (pow_two z).trans (hsq z hz)⟩

/-- Compatibility with two square-zero reductions identifies spectra via the actual source map. -/
theorem source_comap_isHomeomorph (s : B →+* A) (r : A →+* N) (b : B →+* N)
    (hr : Function.Surjective r) (hb : Function.Surjective b)
    (hra : ∀ z, r z = 0 → z * z = 0) (hbb : ∀ z, b z = 0 → z * z = 0)
    (hs : r.comp s = b) : IsHomeomorph (PrimeSpectrum.comap s) := by
  have hR := comap_isHomeomorph r hr hra
  have hB := comap_isHomeomorph b hb hbb
  let e := hR.homeomorph (PrimeSpectrum.comap r)
  have he : PrimeSpectrum.comap s = PrimeSpectrum.comap b ∘ e.symm := by
    funext x
    obtain ⟨y, rfl⟩ := hR.surjective x
    change PrimeSpectrum.comap s (e y) = PrimeSpectrum.comap b (e.symm (e y))
    rw [e.symm_apply_apply]
    exact congrFun (PrimeSpectrum.comap_comp s r).symm y |>.trans
      (congrArg (fun f ↦ PrimeSpectrum.comap f y) hs)
  rw [he]
  exact hB.comp e.symm.isHomeomorph

end FLT.Mazur.SquareZeroReductionKernel
