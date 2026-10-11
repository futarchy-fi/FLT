/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedDegreeProjOverlap

/-!
# Gluing a degree-changing map of Proj schemes

Coverage by the images of positive homogeneous elements is the precise
hypothesis for this construction; no surjectivity on the whole ring is needed.
-/

@[expose] public noncomputable section
open HomogeneousLocalization AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.GradedDegreeProjMap
open GradedDegreeProjOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (f : A →+* B) (r : ℕ) (hf : ∀ d a, a ∈ 𝒜 d → f a ∈ ℬ (r * d)) (hr : 0 < r)
  (hcover : (⨆ i : Σ d : PNat, 𝒜 d, Proj.basicOpen ℬ (f i.2)) = ⊤)

/-- The original image-denominator affine charts cover the whole source Proj. -/
def sourceCover : (Proj ℬ).AffineOpenCover where
  I₀ := Σ d : PNat, 𝒜 d
  X i := .of (Away ℬ (f i.2))
  f i := Proj.awayι ℬ (f i.2) (hf _ _ i.2.property) (Nat.mul_pos hr i.1.property)
  idx x := (TopologicalSpace.Opens.mem_iSup.mp
    (hcover.ge (show x ∈ (⊤ : (Proj ℬ).Opens) from trivial))).choose
  covers x := by
    change x ∈ (Proj.awayι ℬ _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (TopologicalSpace.Opens.mem_iSup.mp
      (hcover.ge (show x ∈ (⊤ : (Proj ℬ).Opens) from trivial))).choose_spec

/-- The actual degree-changing chart maps glue to a morphism of the complete Proj schemes. -/
def map : Proj ℬ ⟶ Proj 𝒜 :=
  (sourceCover 𝒜 ℬ f r hf hr hcover).openCover.glueMorphisms
    (fun i ↦ chartMap 𝒜 ℬ f r hf i.2 i.2.property i.1.property)
    (fun i j ↦ chartMap_overlap 𝒜 ℬ f r hf hr i.2.property j.2.property
      i.1.property j.1.property)

/-- The glued morphism has the original fraction map on each image-denominator chart. -/
@[reassoc]
theorem awayι_map {d : ℕ} (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    Proj.awayι ℬ (f s) (hf d s hs) (Nat.mul_pos hr hd) ≫ map 𝒜 ℬ f r hf hr hcover =
      chartMap 𝒜 ℬ f r hf s hs hd :=
  (sourceCover 𝒜 ℬ f r hf hr hcover).openCover.ι_glueMorphisms _ _ ⟨⟨d, hd⟩, ⟨s, hs⟩⟩

/-- The chart formulas determine the global comparison uniquely. -/
theorem map_unique (g : Proj ℬ ⟶ Proj 𝒜)
    (hg : ∀ (d : ℕ) (s : A) (hs : s ∈ 𝒜 d) (hd : 0 < d),
      Proj.awayι ℬ (f s) (hf d s hs) (Nat.mul_pos hr hd) ≫ g =
        chartMap 𝒜 ℬ f r hf s hs hd) : g = map 𝒜 ℬ f r hf hr hcover := by
  apply (sourceCover 𝒜 ℬ f r hf hr hcover).openCover.hom_ext
  intro i
  exact (hg i.1 i.2 i.2.property i.1.property).trans
    (awayι_map 𝒜 ℬ f r hf hr hcover i.2 i.2.property i.1.property).symm

end FLT.Mazur.GradedDegreeProjMap
