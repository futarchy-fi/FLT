/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.AffineGenericClosure
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Finite point kernels cover an affine generic closure

A prime of the actual closure contains the kernel of evaluation at some point.
This is a finite-intersection argument; it asserts no integrality of coordinates.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePointKernelCover

variable {R B K ι : Type*} [CommRing R] [CommRing B] [CommRing K]
  [Algebra R B] [Algebra R K] (f : B →ₐ[R] (ι → K))

/-- Evaluation at a single point of the kernel-quotient closure. -/
def evaluation (i : ι) : AffineGenericClosure.Coordinate f →ₐ[R] K :=
  (Pi.evalAlgHom R (fun _ : ι => K) i).comp (AffineGenericClosure.inclusion f)

/-- Point evaluation on the quotient still evaluates the original function. -/
theorem evaluation_mk (i : ι) (b : B) :
    evaluation f i (Ideal.Quotient.mk _ b) = f b i := rfl

/-- The point kernels intersect to zero because the closure embeds in the point algebra. -/
theorem iInf_kernel : (⨅ i, RingHom.ker (evaluation f i).toRingHom) = ⊥ := by
  apply le_antisymm
  · intro x hx
    apply Ideal.mem_bot.mpr
    apply AffineGenericClosure.inclusion_injective f
    rw [map_zero]
    funext i
    exact (show evaluation f i x = 0 from
      (iInf_le (fun t => RingHom.ker (evaluation f t).toRingHom) i) hx)
  · exact bot_le

/-- Every prime of a finite point closure contains one of the individual point kernels. -/
theorem exists_kernel_le [Finite ι] (q : PrimeSpectrum (AffineGenericClosure.Coordinate f)) :
    ∃ i, RingHom.ker (evaluation f i).toRingHom ≤ q.asIdeal := by
  let _ := Fintype.ofFinite ι
  have hi : Finset.univ.inf (fun i => RingHom.ker (evaluation f i).toRingHom) ≤
      q.asIdeal := by
    simpa only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true, iInf_kernel] using
      (bot_le : (⊥ : Ideal _) ≤ q.asIdeal)
  obtain ⟨i, _, h⟩ := q.isPrime.inf_le'.mp hi
  exact ⟨i, h⟩

end FLT.Mazur.FinitePointKernelCover
