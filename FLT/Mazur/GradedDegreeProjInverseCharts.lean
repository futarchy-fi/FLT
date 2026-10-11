/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedDegreeProjMap

/-!
# Inverse degree-changing charts

When the actual homogeneous fraction maps are bijective, their inverse affine
scheme maps agree on the original Proj overlaps.
-/

@[expose] public noncomputable section
open HomogeneousLocalization AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.GradedDegreeProjInverseCharts
open GradedDegreeProjOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (f : A →+* B) (r : ℕ) (hf : ∀ d a, a ∈ 𝒜 d → f a ∈ ℬ (r * d)) (hr : 0 < r)
  (hb : ∀ (d : ℕ) (s : A), s ∈ 𝒜 d → 0 < d →
    Function.Bijective (GradedLocalizationDegreeMap.awayMap 𝒜 ℬ f r hf s))

/-- The actual fraction map is an isomorphism of affine schemes. -/
def chartIso {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    Spec (.of (Away ℬ (f s))) ≅ Spec (.of (Away 𝒜 s)) := by
  let _ : IsIso (CommRingCat.ofHom
      (GradedLocalizationDegreeMap.awayMap 𝒜 ℬ f r hf s)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hb d s hs hd)
  exact asIso (Spec.map (CommRingCat.ofHom
    (GradedLocalizationDegreeMap.awayMap 𝒜 ℬ f r hf s)))

/-- The affine isomorphism retains the fraction homomorphism as its forward map. -/
theorem chartIso_hom {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    (chartIso 𝒜 ℬ f r hf hb s hs hd).hom =
      Spec.map (CommRingCat.ofHom (GradedLocalizationDegreeMap.awayMap 𝒜 ℬ f r hf s)) := rfl

/-- The inverse local map retains the original source chart inclusion. -/
def inverseChart {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    Spec (.of (Away 𝒜 s)) ⟶ Proj ℬ :=
  (chartIso 𝒜 ℬ f r hf hb s hs hd).inv ≫
    Proj.awayι ℬ (f s) (hf d s hs) (Nat.mul_pos hr hd)

/-- Cancellation of the actual fraction map recovers the original source chart. -/
@[reassoc]
theorem chartIso_hom_inverseChart {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    (chartIso 𝒜 ℬ f r hf hb s hs hd).hom ≫ inverseChart 𝒜 ℬ f r hf hr hb s hs hd =
      Proj.awayι ℬ (f s) (hf d s hs) (Nat.mul_pos hr hd) := by
  simp only [inverseChart, Iso.hom_inv_id_assoc]

/-- Inverse affine maps also commute with restriction to the product chart. -/
@[reassoc]
theorem restriction_inverseChart {d e : ℕ} {s t x : A}
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hd : 0 < d) (hx : x = s * t) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜 ht hx)) ≫
        inverseChart 𝒜 ℬ f r hf hr hb s hs hd =
      inverseChart 𝒜 ℬ f r hf hr hb x (hx ▸ SetLike.mul_mem_graded hs ht)
        (hd.trans_le (Nat.le_add_right d e)) := by
  let ix := chartIso 𝒜 ℬ f r hf hb x (hx ▸ SetLike.mul_mem_graded hs ht)
    (hd.trans_le (Nat.le_add_right d e))
  apply (cancel_epi ix.hom).mp
  have hc := congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k))
    (GradedLocalizationDegreeMap.awayMap_restriction 𝒜 ℬ f r hf hs ht hx)
  simp only [CommRingCat.ofHom_comp, Spec.map_comp] at hc
  rw [← Category.assoc]
  change (Spec.map (CommRingCat.ofHom
    (GradedLocalizationDegreeMap.awayMap 𝒜 ℬ f r hf x)) ≫
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap 𝒜 ht hx))) ≫ _ = _
  rw [hc, Category.assoc]
  change (Spec.map _ ≫ (chartIso 𝒜 ℬ f r hf hb s hs hd).hom ≫ _) =
    ix.hom ≫ ix.inv ≫ _
  rw [chartIso_hom_inverseChart, Iso.hom_inv_id_assoc, Proj.SpecMap_awayMap_awayι]
  rfl

/-- The inverse charts agree on the actual original-Proj fiber products. -/
theorem inverseChart_overlap {d e : ℕ} {s t : A}
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hd : 0 < d) (he : 0 < e) :
    pullback.fst (Proj.awayι 𝒜 s hs hd) (Proj.awayι 𝒜 t ht he) ≫
        inverseChart 𝒜 ℬ f r hf hr hb s hs hd =
      pullback.snd (Proj.awayι 𝒜 s hs hd) (Proj.awayι 𝒜 t ht he) ≫
        inverseChart 𝒜 ℬ f r hf hr hb t ht he := by
  let iso := Proj.pullbackAwayιIso 𝒜 hs hd ht he (show s * t = s * t from rfl)
  apply (cancel_epi iso.inv).mp
  simp only [← Category.assoc, iso, Proj.pullbackAwayιIso_inv_fst,
    Proj.pullbackAwayιIso_inv_snd]
  rw [restriction_inverseChart 𝒜 ℬ f r hf hr hb hs ht hd rfl,
    restriction_inverseChart 𝒜 ℬ f r hf hr hb ht hs he (mul_comm s t)]
  rfl

end FLT.Mazur.GradedDegreeProjInverseCharts
