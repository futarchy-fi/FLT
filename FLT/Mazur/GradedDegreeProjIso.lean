/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedDegreeProjInverseCharts

/-!
# A global Proj isomorphism from degree-changing fractions

The inverse is glued on the original homogeneous charts. The two identities
are checked on their respective whole-Proj covers.
-/

@[expose] public noncomputable section
open HomogeneousLocalization AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.GradedDegreeProjIso
open GradedDegreeProjOverlap GradedDegreeProjInverseCharts
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (f : A →+* B) (r : ℕ) (hf : ∀ d a, a ∈ 𝒜 d → f a ∈ ℬ (r * d)) (hr : 0 < r)
  (hcover : (⨆ i : Σ d : PNat, 𝒜 d, Proj.basicOpen ℬ (f i.2)) = ⊤)
  (hb : ∀ (d : ℕ) (s : A), s ∈ 𝒜 d → 0 < d →
    Function.Bijective (GradedLocalizationDegreeMap.awayMap 𝒜 ℬ f r hf s))

/-- Glue the inverse fractions on the original complete Proj. -/
def inverse : Proj 𝒜 ⟶ Proj ℬ :=
  (Proj.affineOpenCover 𝒜).openCover.glueMorphisms
    (fun i ↦ inverseChart 𝒜 ℬ f r hf hr hb i.2 i.2.property i.1.property)
    (fun i j ↦ inverseChart_overlap 𝒜 ℬ f r hf hr hb i.2.property j.2.property
      i.1.property j.1.property)

/-- The inverse retains the original affine inverse on every homogeneous chart. -/
@[reassoc]
theorem awayι_inverse {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    Proj.awayι 𝒜 s hs hd ≫ inverse 𝒜 ℬ f r hf hr hb =
      inverseChart 𝒜 ℬ f r hf hr hb s hs hd :=
  (Proj.affineOpenCover 𝒜).openCover.ι_glueMorphisms _ _ ⟨⟨d, hd⟩, ⟨s, hs⟩⟩

/-- The forward map and the constructed inverse cancel on the source cover. -/
theorem map_inverse :
    GradedDegreeProjMap.map 𝒜 ℬ f r hf hr hcover ≫ inverse 𝒜 ℬ f r hf hr hb = 𝟙 _ := by
  apply (GradedDegreeProjMap.sourceCover 𝒜 ℬ f r hf hr hcover).openCover.hom_ext
  intro i
  change (Σ d : PNat, 𝒜 d) at i
  change Proj.awayι ℬ (f i.2) (hf _ _ i.2.property)
    (Nat.mul_pos hr i.1.property) ≫ _ =
      Proj.awayι ℬ (f i.2) (hf _ _ i.2.property) (Nat.mul_pos hr i.1.property) ≫ 𝟙 _
  rw [GradedDegreeProjMap.awayι_map_assoc 𝒜 ℬ f r hf hr hcover
    i.2 i.2.property i.1.property, chartMap, Category.assoc,
    awayι_inverse 𝒜 ℬ f r hf hr hb i.2 i.2.property i.1.property]
  change (chartIso 𝒜 ℬ f r hf hb i.2 i.2.property i.1.property).hom ≫ _ = _
  rw [chartIso_hom_inverseChart, Category.comp_id]

/-- The inverse and forward map cancel on the original target cover. -/
theorem inverse_map :
    inverse 𝒜 ℬ f r hf hr hb ≫ GradedDegreeProjMap.map 𝒜 ℬ f r hf hr hcover = 𝟙 _ := by
  apply (Proj.affineOpenCover 𝒜).openCover.hom_ext
  intro i
  change (Σ d : PNat, 𝒜 d) at i
  change Proj.awayι 𝒜 (i.2 : A) i.2.property i.1.property ≫ _ =
    Proj.awayι 𝒜 (i.2 : A) i.2.property i.1.property ≫ 𝟙 _
  rw [awayι_inverse_assoc 𝒜 ℬ f r hf hr hb i.2 i.2.property i.1.property,
    inverseChart, Category.assoc,
    GradedDegreeProjMap.awayι_map 𝒜 ℬ f r hf hr hcover i.2 i.2.property i.1.property,
    chartMap]
  change (chartIso 𝒜 ℬ f r hf hb i.2 i.2.property i.1.property).inv ≫
    (chartIso 𝒜 ℬ f r hf hb i.2 i.2.property i.1.property).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc, Category.comp_id]

/-- Bijective fraction maps and whole-Proj coverage give the global isomorphism. -/
def iso : Proj ℬ ≅ Proj 𝒜 where
  hom := GradedDegreeProjMap.map 𝒜 ℬ f r hf hr hcover
  inv := inverse 𝒜 ℬ f r hf hr hb
  hom_inv_id := map_inverse 𝒜 ℬ f r hf hr hcover hb
  inv_hom_id := inverse_map 𝒜 ℬ f r hf hr hcover hb

/-- The isomorphism's forward map is the original glued fraction morphism. -/
theorem iso_hom : (iso 𝒜 ℬ f r hf hr hcover hb).hom =
    GradedDegreeProjMap.map 𝒜 ℬ f r hf hr hcover := rfl

end FLT.Mazur.GradedDegreeProjIso
