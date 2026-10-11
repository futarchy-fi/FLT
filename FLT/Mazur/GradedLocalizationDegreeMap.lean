/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Homogeneous localization maps with a change of degree

A ring map that multiplies homogeneous degrees still maps degree-zero fractions.
This is the local algebra needed for comparisons of different Veronese steps.
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
  {P : Submonoid A} {Q : Submonoid B} (hPQ : P ≤ Q.comap f)

/-- Equal-degree fractions map to equal-degree fractions at the scaled degree. -/
def mapValue : HomogeneousLocalization 𝒜 P → HomogeneousLocalization ℬ Q :=
  Quotient.map'
    (fun x ↦ ⟨r * x.deg, ⟨f x.num, hf _ _ x.num.property⟩,
      ⟨f x.den, hf _ _ x.den.property⟩, hPQ x.den_mem⟩)
    fun x y (e : x.embedding = y.embedding) ↦ by
      apply_fun IsLocalization.map (Localization Q) f hPQ at e
      simp_rw [NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
      exact e

omit [AddSubgroupClass σ A] [AddSubgroupClass τ B] [GradedRing 𝒜] [GradedRing ℬ] in
/-- Forgetting the degree gives the original localization map. -/
theorem mapValue_val (x : HomogeneousLocalization 𝒜 P) :
    (mapValue 𝒜 ℬ f r hf hPQ x).val =
      IsLocalization.map (Localization Q) f hPQ x.val := by
  obtain ⟨x, rfl⟩ := HomogeneousLocalization.mk_surjective x
  change Localization.mk _ _ = IsLocalization.map (Localization Q) f hPQ (Localization.mk _ _)
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk']

/-- The fraction map is a ring homomorphism despite its change of homogeneous degree. -/
def map : HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q where
  toFun := mapValue 𝒜 ℬ f r hf hPQ
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    rw [mapValue_val, val_zero, map_zero, val_zero]
  map_one' := by
    apply HomogeneousLocalization.val_injective
    rw [mapValue_val, val_one, map_one, val_one]
  map_add' x y := by
    apply HomogeneousLocalization.val_injective
    rw [mapValue_val, val_add, map_add, val_add, mapValue_val, mapValue_val]
  map_mul' x y := by
    apply HomogeneousLocalization.val_injective
    rw [mapValue_val, val_mul, map_mul, val_mul, mapValue_val, mapValue_val]

/-- A Veronese degree change gives the actual map of standard affine chart rings. -/
def awayMap (s : A) : Away 𝒜 s →+* Away ℬ (f s) :=
  map 𝒜 ℬ f r hf (by
    rintro _ ⟨k, rfl⟩
    exact ⟨k, (map_pow f s k).symm⟩)

/-- A chart fraction keeps its original numerator and denominator under the ring map. -/
theorem awayMap_mk {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (k : ℕ)
    (a : A) (ha : a ∈ 𝒜 (k • d)) :
    awayMap 𝒜 ℬ f r hf s (Away.mk 𝒜 hs k a ha) =
      Away.mk ℬ (hf d s hs) k (f a)
        (by simpa only [smul_eq_mul, Nat.mul_left_comm] using hf (k • d) a ha) := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk]
  change (mapValue 𝒜 ℬ f r hf (P := .powers s) (Q := .powers (f s))
    (by rintro _ ⟨j, rfl⟩; exact ⟨j, (map_pow f s j).symm⟩) (Away.mk 𝒜 hs k a ha)).val = _
  rw [mapValue_val, Away.val_mk]
  simp only [Localization.mk_eq_mk', IsLocalization.map_mk', map_pow]

/-- Injectivity is retained when the target denominators are exactly the original images. -/
theorem map_injective (hi : Function.Injective f) (hQ : Q = P.map f) :
    Function.Injective (map 𝒜 ℬ f r hf hPQ) := by
  subst Q
  intro x y he
  apply HomogeneousLocalization.val_injective
  apply IsLocalization.map_injective_of_injective P (Localization P) (Localization (P.map f)) hi
  have hv := congrArg HomogeneousLocalization.val he
  change (mapValue 𝒜 ℬ f r hf hPQ x).val = (mapValue 𝒜 ℬ f r hf hPQ y).val at hv
  simpa only [mapValue_val] using hv

/-- Injective degree-changing ring maps induce injective maps on the original affine charts. -/
theorem awayMap_injective (hi : Function.Injective f) (s : A) :
    Function.Injective (awayMap 𝒜 ℬ f r hf s) :=
  map_injective 𝒜 ℬ f r hf _ hi (Submonoid.map_powers f s).symm

/-- Lifting the homogeneous numerators proves surjectivity of the actual chart map. -/
theorem awayMap_surjective {s : A} {d : ℕ} (hs : s ∈ 𝒜 d)
    (hl : ∀ k b, b ∈ ℬ (r * (k * d)) → ∃ a ∈ 𝒜 (k * d), f a = b) :
    Function.Surjective (awayMap 𝒜 ℬ f r hf s) := by
  intro z
  obtain ⟨k, b, hb, rfl⟩ := Away.mk_surjective ℬ (hf d s hs) z
  obtain ⟨a, ha, rfl⟩ := hl k b
    (by simpa only [smul_eq_mul, Nat.mul_left_comm] using hb)
  exact ⟨Away.mk 𝒜 hs k a ha, awayMap_mk 𝒜 ℬ f r hf hs k a ha⟩

end FLT.Mazur.GradedLocalizationDegreeMap
