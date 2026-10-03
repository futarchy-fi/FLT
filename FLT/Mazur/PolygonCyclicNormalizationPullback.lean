/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicNormalizationRanges
/-!
# Cartesian normalization charts of the cyclic polygon

The two affine branches over a node chart embed openly in the normalization
coproduct, in distinct adjacent components. The computed inverse-image range
identifies their square with the pullback of the global normalization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace FLT.Mazur.PolygonCyclicNormalizationPullback
open PolygonCyclicAtlas PolygonCyclicNormalizationRanges
variable (K : Type u) [Field K] (n : ℕ) (hn : 2 ≤ n)

/-- The normalization coproduct in schemes. -/
abbrev components := ∐ fun _ : Fin n ↦ ProjectiveLine.scheme K

/-- The specified component maps assembled in schemes. -/
def normalization : components K n ⟶ scheme K n hn :=
  Sigma.desc (componentMap K n hn)

/-- The left affine chart of the component at a node. -/
def firstLift (j : Fin n) : ProjectiveLine.chart K ⟶ components K n :=
  ProjectiveLine.left K ≫ Sigma.ι (fun _ : Fin n ↦ ProjectiveLine.scheme K) j

/-- The right affine chart of the successor component. -/
def secondLift (j : Fin n) : ProjectiveLine.chart K ⟶ components K n :=
  ProjectiveLine.right K ≫ Sigma.ι (fun _ : Fin n ↦ ProjectiveLine.scheme K) (finRotate n j)

instance firstLift_open (j : Fin n) : IsOpenImmersion (firstLift K n j) := by
  unfold firstLift
  infer_instance
instance secondLift_open (j : Fin n) : IsOpenImmersion (secondLift K n j) := by
  unfold secondLift
  infer_instance

/-- The two adjacent affine charts inside the normalization coproduct. -/
def chartLift (_hn : 2 ≤ n) (j : Fin n) :
    ProjectiveLine.chart K ⨿ ProjectiveLine.chart K ⟶ components K n :=
  coprod.desc (firstLift K n j) (secondLift K n j)

include hn in
theorem successor_ne (j : Fin n) : j ≠ finRotate n j := by
  intro h
  apply prev_ne hn j
  exact (congrArg (finRotate n).symm h).trans (Equiv.symm_apply_apply _ _)

include hn in
theorem lifts_ne (j : Fin n) (a b : ProjectiveLine.chart K) :
    firstLift K n j a ≠ secondLift K n j b := by
  intro h
  have he := (sigmaι_eq_iff (fun _ : Fin n ↦ ProjectiveLine.scheme K)
    j (finRotate n j) (ProjectiveLine.left K a) (ProjectiveLine.right K b)).mp h
  exact successor_ne n hn j (congrArg Sigma.fst he)

theorem chartLift_injective (j : Fin n) : Function.Injective (chartLift K n hn j) := by
  intro a b hab
  obtain ⟨a | a, rfl⟩ := (coprodMk _ _).surjective a <;>
    obtain ⟨b | b, rfl⟩ := (coprodMk _ _).surjective b
  · simp only [coprodMk_inl, ← Scheme.Hom.comp_apply, chartLift, coprod.inl_desc] at hab ⊢
    exact congrArg _ ((firstLift K n j).isOpenEmbedding.injective hab)
  · simp only [coprodMk_inl, coprodMk_inr,
      ← Scheme.Hom.comp_apply, chartLift, coprod.inl_desc, coprod.inr_desc] at hab
    exact (lifts_ne K n hn j a b hab).elim
  · simp only [coprodMk_inl, coprodMk_inr,
      ← Scheme.Hom.comp_apply, chartLift, coprod.inl_desc, coprod.inr_desc] at hab
    exact (lifts_ne K n hn j b a hab.symm).elim
  · simp only [coprodMk_inr, ← Scheme.Hom.comp_apply, chartLift, coprod.inr_desc] at hab ⊢
    exact congrArg _ ((secondLift K n j).isOpenEmbedding.injective hab)

instance chartLift_open (j : Fin n) : IsOpenImmersion (chartLift K n hn j) := by
  apply IsOpenImmersion.of_openCover_source _ (coprodOpenCover.{u, 0} _ _)
    (chartLift_injective K n hn j)
  intro i
  rcases i with _ | _
  · change IsOpenImmersion (coprod.inl ≫ chartLift K n hn j)
    simp only [chartLift, coprod.inl_desc]
    infer_instance
  · change IsOpenImmersion (coprod.inr ≫ chartLift K n hn j)
    simp only [chartLift, coprod.inr_desc]
    infer_instance

/-- The two full branches mapping to the affine node. -/
def affineNormalization : ProjectiveLine.chart K ⨿ ProjectiveLine.chart K ⟶
    PolygonNodeBranches.node K := coprod.desc (firstBranch K) (secondBranch K)

@[reassoc] theorem chartLift_normalization (j : Fin n) :
    chartLift K n hn j ≫ normalization K n hn = affineNormalization K ≫ chart K n hn j := by
  apply coprod.hom_ext
  · simp [chartLift, firstLift, normalization, affineNormalization]
  · simp only [chartLift, coprod.inr_desc_assoc, secondLift, Category.assoc,
      normalization, Sigma.ι_comp_desc, right_componentMap, Equiv.symm_apply_apply,
      affineNormalization]

theorem preimage_chart (j : Fin n) :
    normalization K n hn ⁻¹ᵁ (chart K n hn j).opensRange = (chartLift K n hn j).opensRange := by
  ext z
  change normalization K n hn z ∈ Set.range (chart K n hn j) ↔
    z ∈ Set.range (chartLift K n hn j)
  constructor
  · intro hz
    obtain ⟨i, z, rfl⟩ := (sigmaOpenCover (fun _ : Fin n ↦ ProjectiveLine.scheme K)).exists_eq z
    change normalization K n hn
      (Sigma.ι (fun _ : Fin n ↦ ProjectiveLine.scheme K) i z) ∈ _ at hz
    rw [← Scheme.Hom.comp_apply, normalization, Sigma.ι_comp_desc] at hz
    change Sigma.ι (fun _ : Fin n ↦ ProjectiveLine.scheme K) i z ∈ _
    rcases component_preimage K n hn i j z hz with ⟨a, hi, ha⟩ | ⟨a, hi, ha⟩
    · subst i
      rw [← ha]
      refine ⟨(coprod.inl : ProjectiveLine.chart K ⟶
        ProjectiveLine.chart K ⨿ ProjectiveLine.chart K) a, ?_⟩
      change (coprod.inl ≫ chartLift K n hn j) a = _
      simp [chartLift, firstLift]
    · subst i
      rw [← ha]
      refine ⟨(coprod.inr : ProjectiveLine.chart K ⟶
        ProjectiveLine.chart K ⨿ ProjectiveLine.chart K) a, ?_⟩
      change (coprod.inr ≫ chartLift K n hn j) a = _
      simp [chartLift, secondLift]
  · rintro ⟨a, rfl⟩
    exact ⟨affineNormalization K a,
      (congrArg (fun f ↦ f a) (chartLift_normalization K n hn j)).symm⟩

/-- The two affine branches are precisely the normalization over this node chart. -/
theorem isPullback (j : Fin n) : IsPullback (affineNormalization K) (chartLift K n hn j)
    (chart K n hn j) (normalization K n hn) :=
  IsOpenImmersion.isPullback _ _ _ _ (chartLift_normalization K n hn j) (preimage_chart K n hn j)
end FLT.Mazur.PolygonCyclicNormalizationPullback
