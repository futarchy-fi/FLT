/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedLocalizationDegreeMap

/-!
# Degree-changing fractions commute with chart restrictions

The standard restriction multiplies a fraction's numerator and denominator by
powers of the second chart denominator. Applying a degree-changing ring map
before or after that operation gives the same fraction on the overlap.
-/

@[expose] public noncomputable section
open HomogeneousLocalization
namespace FLT.Mazur.GradedLocalizationDegreeMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (f : A →+* B) (r : ℕ) (hf : ∀ d a, a ∈ 𝒜 d → f a ∈ ℬ (r * d))

/-- Actual homogeneous fractions commute with restriction to a product chart. -/
theorem awayMap_restriction {d e : ℕ} {s t x : A}
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hx : x = s * t) :
    (awayMap 𝒜 ℬ f r hf x).comp (HomogeneousLocalization.awayMap 𝒜 ht hx) =
      (HomogeneousLocalization.awayMap ℬ (hf e t ht)
        (show f x = f s * f t by rw [hx, map_mul])).comp
        (awayMap 𝒜 ℬ f r hf s) := by
  ext z
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs z
  simp only [RingHom.comp_apply, HomogeneousLocalization.awayMap_mk, awayMap_mk]
  simp only [Away.val_mk, map_mul, map_pow]

/-- The same compatibility in pointwise form, usable after taking spectra. -/
theorem awayMap_restriction_apply {d e : ℕ} {s t x : A}
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hx : x = s * t) (z : Away 𝒜 s) :
    awayMap 𝒜 ℬ f r hf x (HomogeneousLocalization.awayMap 𝒜 ht hx z) =
      HomogeneousLocalization.awayMap ℬ (hf e t ht)
        (show f x = f s * f t by rw [hx, map_mul]) (awayMap 𝒜 ℬ f r hf s z) :=
  DFunLike.congr_fun (awayMap_restriction 𝒜 ℬ f r hf hs ht hx) z

end FLT.Mazur.GradedLocalizationDegreeMap
