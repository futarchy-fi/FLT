/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodePinchingExistence

/-!
# Arbitrary-target descent for the affine node

Normalization branch maps agreeing at the origin descend uniquely. Uniqueness
uses a common affine neighborhood of the node image, without separatedness.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial TopologicalSpace

universe u

namespace FLT.Mazur.NodePinchingDescent

open PolygonNodeEqualizer PolygonNodePresentation NodeLocalDescent NodeLocalizedEqualizer

variable (K : Type u) [Field K]

/-- A neighborhood of the node contains a principal neighborhood with value one. -/
theorem principal_neighborhood (V : (PolygonNodeBranches.node K).Opens)
    (hv : aOrigin K (⊥ : PrimeSpectrum K) ∈ V) :
    ∃ s : A (R := K), aEval s = 1 ∧ PrimeSpectrum.basicOpen s ≤ V := by
  obtain ⟨_, ⟨p, rfl⟩, hp, hpV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hv V.isOpen
  have hp' : aEval p ≠ 0 := by
    change aEval p ∉ (⊥ : Ideal K) at hp
    simpa using hp
  refine ⟨algebraMap K _ (aEval p)⁻¹ * p, ?_, ?_⟩
  · simp [hp']
  · exact (PrimeSpectrum.basicOpen_mul_le_right _ _).trans hpV

/-- Arbitrary-target morphisms from the node are determined by their two branches. -/
theorem hom_ext {Y : Scheme.{u}} (d e : PolygonNodeBranches.node K ⟶ Y)
    (h₁ : PolygonCyclicAtlas.firstBranch K ≫ d = PolygonCyclicAtlas.firstBranch K ≫ e)
    (h₂ : PolygonCyclicAtlas.secondBranch K ≫ d = PolygonCyclicAtlas.secondBranch K ≫ e) :
    d = e := by
  let o := aOrigin K (⊥ : PrimeSpectrum K)
  have ho : d o = e o := by
    have h := congrArg (fun f ↦ ProjectiveLine.chartZero K ≫ f) h₁
    simpa only [← Category.assoc, PolygonCyclicAtlas.zero_firstBranch,
      Scheme.Hom.comp_apply, o] using
      congrArg (fun f ↦ f (⊥ : PrimeSpectrum K)) h
  obtain ⟨U, hU, hoU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := d o) (by trivial)
  obtain ⟨s, hs, hV⟩ := principal_neighborhood K (d ⁻¹ᵁ U ⊓ e ⁻¹ᵁ U)
    (show d o ∈ U ∧ e o ∈ U from ⟨hoU, by rwa [← ho]⟩)
  have hr (a : PolygonNodeBranches.node K ⟶ Y)
      (ha : PrimeSpectrum.basicOpen s ≤ a ⁻¹ᵁ U) :
      Set.range (neighborhood K s hs ≫ a) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : neighborhood K s hs z ∈ Set.range (neighborhood K s hs) := ⟨z, rfl⟩
    rw [range_neighborhood] at hz
    exact ha hz
  let d' := IsOpenImmersion.lift U.ι (neighborhood K s hs ≫ d) (hr d (hV.trans inf_le_left))
  let e' := IsOpenImmersion.lift U.ι (neighborhood K s hs ≫ e) (hr e (hV.trans inf_le_right))
  have hd' : d' ≫ U.ι = neighborhood K s hs ≫ d := IsOpenImmersion.lift_fac ..
  have he' : e' ≫ U.ι = neighborhood K s hs ≫ e := IsOpenImmersion.lift_fac ..
  have hb₁ : firstBranch K s hs ≫ d' = firstBranch K s hs ≫ e' := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, Category.assoc, hd', he']
    simp only [firstBranch_neighborhood_assoc, h₁]
  have hb₂ : secondBranch K s hs ≫ d' = secondBranch K s hs ≫ e' := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, Category.assoc, hd', he']
    simp only [secondBranch_neighborhood_assoc, h₂]
  have w : firstOrigin K s hs ≫ firstBranch K s hs =
      secondOrigin K s hs ≫ secondBranch K s hs := by
    rw [firstOrigin, firstBranch, secondOrigin, secondBranch, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a ↦ a.property)
  let : IsAffine U := hU
  obtain ⟨_, _, hu⟩ := desc_affine K s hs (firstBranch K s hs ≫ d')
    (secondBranch K s hs ≫ d') (by rw [← Category.assoc, ← Category.assoc, w])
  have hde : d' = e' := (hu d' ⟨rfl, rfl⟩).trans (hu e' ⟨hb₁.symm, hb₂.symm⟩).symm
  apply (TernaryOpenDescent.cover (neighborhood K s hs) (PolygonNodeBranches.left K)
    (PolygonNodeBranches.right K) (covers K s hs)).hom_ext
  rintro (_ | (_ | _))
  · change neighborhood K s hs ≫ d = neighborhood K s hs ≫ e
    rw [← hd', ← he', hde]
  · change PolygonNodeBranches.left K ≫ d = PolygonNodeBranches.left K ≫ e
    rw [← PolygonCyclicAtlas.overlap_firstBranch, Category.assoc, Category.assoc, h₁]
  · change PolygonNodeBranches.right K ≫ d = PolygonNodeBranches.right K ≫ e
    rw [← PolygonCyclicAtlas.overlap_secondBranch, Category.assoc, Category.assoc, h₂]

/-- The exact node descent statement, with no affine hypothesis on the target. -/
theorem node_desc {Y : Scheme.{u}} (f g : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.chartZero K ≫ f = ProjectiveLine.chartZero K ≫ g) :
    ∃! d : PolygonNodeBranches.node K ⟶ Y,
      PolygonCyclicAtlas.firstBranch K ≫ d = f ∧
      PolygonCyclicAtlas.secondBranch K ≫ d = g := by
  obtain ⟨d, hd₁, hd₂⟩ := NodePinchingExistence.exists_desc K f g w
  exact ⟨d, ⟨hd₁, hd₂⟩, fun e he ↦ hom_ext K e d
    (he.1.trans hd₁.symm) (he.2.trans hd₂.symm)⟩

end FLT.Mazur.NodePinchingDescent
