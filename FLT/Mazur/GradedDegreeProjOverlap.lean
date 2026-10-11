/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedLocalizationDegreeRestriction
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Degree-changing Proj chart maps agree on overlaps

The scheme maps are induced by the original fraction maps. Their compatibility
is proved on the actual fiber products of the image-denominator charts.
-/

@[expose] public noncomputable section
open HomogeneousLocalization AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.GradedDegreeProjOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (f : A →+* B) (r : ℕ) (hf : ∀ d a, a ∈ 𝒜 d → f a ∈ ℬ (r * d))

/-- The actual fraction map followed by the original target chart inclusion. -/
def chartMap {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    Spec (.of (Away ℬ (f s))) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (GradedLocalizationDegreeMap.awayMap 𝒜 ℬ f r hf s)) ≫
    Proj.awayι 𝒜 s hs hd

/-- Restriction to a product chart retains the original scheme map. -/
@[reassoc]
theorem restriction_chartMap {d e : ℕ} {s t x : A}
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hd : 0 < d) (hx : x = s * t) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap ℬ (hf e t ht)
      (show f x = f s * f t by rw [hx, map_mul]))) ≫ chartMap 𝒜 ℬ f r hf s hs hd =
        chartMap 𝒜 ℬ f r hf x (hx ▸ SetLike.mul_mem_graded hs ht)
          (hd.trans_le (Nat.le_add_right d e)) := by
  unfold chartMap
  rw [← Category.assoc, ← Spec.map_comp]
  have he := GradedLocalizationDegreeMap.awayMap_restriction 𝒜 ℬ f r hf hs ht hx
  have hc := congrArg CommRingCat.ofHom he
  simp only [CommRingCat.ofHom_comp] at hc
  rw [← hc, Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]

/-- The local maps agree on the actual fiber product of their source charts. -/
theorem chartMap_overlap (hr : 0 < r) {d e : ℕ} {s t : A}
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hd : 0 < d) (he : 0 < e) :
    pullback.fst (Proj.awayι ℬ (f s) (hf d s hs) (Nat.mul_pos hr hd))
        (Proj.awayι ℬ (f t) (hf e t ht) (Nat.mul_pos hr he)) ≫
          chartMap 𝒜 ℬ f r hf s hs hd =
      pullback.snd (Proj.awayι ℬ (f s) (hf d s hs) (Nat.mul_pos hr hd))
        (Proj.awayι ℬ (f t) (hf e t ht) (Nat.mul_pos hr he)) ≫
          chartMap 𝒜 ℬ f r hf t ht he := by
  let iso := Proj.pullbackAwayιIso ℬ (hf d s hs) (Nat.mul_pos hr hd)
    (hf e t ht) (Nat.mul_pos hr he) (map_mul f s t)
  apply (cancel_epi iso.inv).mp
  simp only [← Category.assoc, iso, Proj.pullbackAwayιIso_inv_fst,
    Proj.pullbackAwayιIso_inv_snd]
  rw [restriction_chartMap 𝒜 ℬ f r hf hs ht hd rfl,
    restriction_chartMap 𝒜 ℬ f r hf ht hs he (mul_comm s t)]
  rfl

end FLT.Mazur.GradedDegreeProjOverlap
