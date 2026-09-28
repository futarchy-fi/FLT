/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.FrobeniusImage
public import Mathlib.Algebra.MvPolynomial.Eval

/-! # Coordinate powers generate the Frobenius image -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {k A ι : Type*} [Field k] [CommRing A] [Algebra k A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p] [PerfectRing k p]

/-- Powers of a generating coordinate family generate the Frobenius image. -/
theorem aeval_frobeniusCoordinates_surjective (x : ι → A)
    (hx : Function.Surjective (aeval (R := k) x))
    (z : ι → Algebra.frobeniusImage k A p 1) (hz : ∀ i, (z i : A) = x i ^ p) :
    Function.Surjective (aeval (R := k) z) := by
  let F := Algebra.frobeniusImage k A p 1
  have he : F.val.toRingHom.comp
        ((aeval (R := k) z).toRingHom.comp (map (frobenius k p))) =
      (frobenius A p).comp (aeval (R := k) x).toRingHom := by
    apply ringHom_ext
    · intro c
      change (aeval z (map (frobenius k p) (C c)) : A) = (aeval x (C c)) ^ p
      simp [frobenius_def]
    · intro i
      change (aeval z (map (frobenius k p) (X i)) : A) = (aeval x (X i)) ^ p
      simpa using hz i
  intro c
  obtain ⟨a, ha⟩ := c.property
  obtain ⟨f, hf⟩ := hx a
  refine ⟨map (frobenius k p) f, ?_⟩
  apply Subtype.ext
  have h := DFunLike.congr_fun he f
  change (aeval z (map (frobenius k p) f) : A) = (aeval x f) ^ p at h
  rw [h, hf]
  simpa only [iterateFrobenius_def, pow_one] using ha

end MvPolynomial
