/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveUnitChartEvaluation
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Evaluation on arbitrary homogeneous projective charts

A polynomial evaluation taking a homogeneous denominator to a unit evaluates
its degree-zero localization. This construction commutes with graded pullback
and with extension of the test ring.
-/

@[expose] public noncomputable section
open MvPolynomial HomogeneousLocalization
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type u) [CommRing R] (ι : Type u)
variable {S : Type u} [CommRing S]

/-- Evaluate degree-zero fractions at an invertible homogeneous denominator. -/
def homogeneousEval (F : MvPolynomial ι R →+* S) (s : MvPolynomial ι R)
    (a : Sˣ) (hs : F s = a) : Away (grading R ι) s →+* S :=
  (Localization.awayLift F s (hs ▸ a.isUnit)).comp
    (algebraMap _ (Localization.Away s))

/-- Evaluation is the numerator divided by the appropriate denominator power. -/
lemma homogeneousEval_mk (F : MvPolynomial ι R →+* S) (s : MvPolynomial ι R)
    (a : Sˣ) (hs : F s = a) {m : ℕ} (hm : s ∈ grading R ι m)
    (d : ℕ) (p : MvPolynomial ι R) (hp : p ∈ grading R ι (d • m)) :
    homogeneousEval R ι F s a hs (Away.mk _ hm d p hp) = F p * (↑a⁻¹ : S) ^ d := by
  change Localization.awayLift F s (hs ▸ a.isUnit) (Localization.mk p _) = _
  exact Localization.awayLift_mk F s p (↑a⁻¹ : S) (by rw [hs]; simp) d

/-- On a standard chart this recovers evaluation by normalized coordinates. -/
lemma homogeneousEval_variable (f : R →+* S) (x : ι → S) (i : ι) (a : Sˣ)
    (hi : x i = a) :
    homogeneousEval R ι (eval₂Hom f x) (X i) a (by simpa using hi) =
      unitChartEval R ι f x i a hi := by
  ext z
  obtain ⟨d, p, hp, rfl⟩ := Away.mk_surjective (grading R ι) (isHomogeneous_X R i) z
  rw [homogeneousEval_mk, unitChartEval_mk]
  exact mul_comm _ _

/-- Graded pullback commutes with evaluating the actual homogeneous fractions. -/
lemma homogeneousEval_gradedMap {T : Type u} [CommRing T] {κ : Type u}
    (g : grading T κ →+*ᵍ grading R ι) (F : MvPolynomial ι R →+* S)
    (s : MvPolynomial κ T) (a : Sˣ) (hs : F (g s) = a)
    {m : ℕ} (hm : s ∈ grading T κ m) :
    (homogeneousEval R ι F (g s) a hs).comp (Away.map g s) =
      homogeneousEval T κ (F.comp g.toRingHom) s a hs := by
  ext z
  obtain ⟨d, p, hp, rfl⟩ := Away.mk_surjective (grading T κ) hm z
  simp only [RingHom.comp_apply, Away.map_mk, homogeneousEval_mk]
  rfl

/-- Evaluation is natural for homomorphisms of the affine test ring. -/
lemma homogeneousEval_map {T : Type u} [CommRing T] (g : S →+* T)
    (F : MvPolynomial ι R →+* S) (s : MvPolynomial ι R)
    (a : Sˣ) (hs : F s = a) {m : ℕ} (hm : s ∈ grading R ι m) :
    g.comp (homogeneousEval R ι F s a hs) =
      homogeneousEval R ι (g.comp F) s (Units.map g a) (by simp [hs]) := by
  ext z
  obtain ⟨d, p, hp, rfl⟩ := Away.mk_surjective (grading R ι) hm z
  simp only [RingHom.comp_apply, homogeneousEval_mk, map_mul, map_pow]
  rfl

end FLT.Mazur.ProjectiveSpace
