/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneratorDenominatorLocalization

/-!
# Lifting the exact source denominator after generator recovery

Once the original algebra generators and the extra denominator inverse are in
the image, the original source denominator has a lift. Inverting that lift
produces a surjective map to the doubly localized source ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.ExactSourceDenominatorLift
open PrincipalLocalizationGeneration
variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S]
  (s : R) (t : Localization.Away s)
  (f : S →ₐ[K] Localization.Away t)

/-- Original generators in the image put every original ring element in the image. -/
lemma original_mem (G : Set R) (hG : Algebra.adjoin K G = ⊤)
    (hg : ∀ x ∈ G, algebraMap R (Localization.Away t) x ∈ f.range) (b : R) :
    algebraMap R (Localization.Away t) b ∈ f.range := by
  have hh : Algebra.adjoin K G ≤
      f.range.comap (IsScalarTower.toAlgHom K R (Localization.Away t)) :=
    Algebra.adjoin_le hg
  rw [hG] at hh
  exact hh (show b ∈ (⊤ : Subalgebra K R) from trivial)

/-- A lift of the exact chosen source denominator is a unit after applying f. -/
lemma lift_isUnit (b : S) (hb : f b = algebraMap R (Localization.Away t) s) :
    IsUnit (f b) := by
  rw [hb, IsScalarTower.algebraMap_apply R (Localization.Away s) (Localization.Away t)]
  exact (IsLocalization.Away.algebraMap_isUnit s).map _

/-- The compatible target refinement obtained by inverting that exact lift. -/
def refinedMap (b : S) (hb : f b = algebraMap R (Localization.Away t) s) :
    Localization.Away b →ₐ[K] Localization.Away t :=
  IsLocalization.Away.liftAlgHom b (lift_isUnit s t f b hb)

/-- The refinement agrees with f on numerators. -/
lemma refinedMap_algebraMap (b : S) (hb : f b = algebraMap R (Localization.Away t) s)
    (a : S) : refinedMap s t f b hb (algebraMap S (Localization.Away b) a) = f a := by
  exact IsLocalization.Away.lift_eq b (lift_isUnit s t f b hb) a

/-- Inverting the lift supplies precisely the missing source inverse. -/
lemma refinedMap_inverse (b : S) (hb : f b = algebraMap R (Localization.Away t) s) :
    refinedMap s t f b hb (IsLocalization.Away.invSelf b) =
      algebraMap (Localization.Away s) (Localization.Away t) (IsLocalization.Away.invSelf s) := by
  apply (lift_isUnit s t f b hb).mul_left_cancel
  calc
    _ = refinedMap s t f b hb
        (algebraMap S (Localization.Away b) b * IsLocalization.Away.invSelf b) := by
      rw [map_mul, refinedMap_algebraMap]
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = _ := by
      rw [hb, IsScalarTower.algebraMap_apply R (Localization.Away s) (Localization.Away t),
        ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

/-- The exact lift and its compatible localization give a surjective chart map. -/
theorem exists_surjective_refinement (G : Set R) (hG : Algebra.adjoin K G = ⊤)
    (hg : ∀ x ∈ G, algebraMap R (Localization.Away t) x ∈ f.range)
    (ht : IsLocalization.Away.invSelf t ∈ f.range) :
    ∃ (b : S) (hb : f b = algebraMap R (Localization.Away t) s),
      Function.Surjective (refinedMap s t f b hb) := by
  obtain ⟨b, hb⟩ := original_mem s t f G hG hg s
  refine ⟨b, hb, ?_⟩
  let F := refinedMap s t f b hb
  have hf : f.range ≤ F.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨algebraMap S (Localization.Away b) a, refinedMap_algebraMap s t f b hb a⟩
  have hi : algebraMap (Localization.Away s) (Localization.Away t)
      (IsLocalization.Away.invSelf s) ∈ F.range :=
    ⟨IsLocalization.Away.invSelf b, refinedMap_inverse s t f b hb⟩
  have hr (a : Localization.Away s) :
      algebraMap (Localization.Away s) (Localization.Away t) a ∈ F.range := by
    obtain ⟨r, k, rfl⟩ := fraction_representation s a
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    exact F.range.mul_mem (hf (original_mem s t f G hG hg r)) (F.range.pow_mem hi k)
  intro z
  obtain ⟨a, k, rfl⟩ := fraction_representation t z
  exact F.range.mul_mem (hr a) (F.range.pow_mem (hf ht) k)

end FLT.Mazur.ExactSourceDenominatorLift
