/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonLocalDescent
public import FLT.Mazur.NodePinchingExistence
public import FLT.Mazur.OneGonAffineCover

/-!
# Arbitrary-target descent for the affine one-gon chart

A normalization map identifying the two endpoints descends uniquely, using a
saturated node neighborhood and the conductor complement.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial TopologicalSpace

universe u

namespace FLT.Mazur.OneGonPinchingDescent

open PolygonNodePresentation OneGonLocalDescent OneGonLocalizedEqualizer PinchingAffineDescent
open NodeLocalDescent (branchOpen)
open OneGonAffineCover (punctureOpen)

variable (K : Type u) [Field K]

@[reassoc (attr := simp)]
theorem puncture_oneBranch : punctureOpen K ≫ oneBranch K = bPuncture K := by
  rw [OneGonAffineCover.punctureOpen, oneBranch, bPuncture, ← Spec.map_comp]
  rfl

/-- The normalized neighborhood and conductor complement cover the normalization. -/
theorem line_covers (s : B (R := K)) (hs : bEval s = 1) (z : ProjectiveLine.chart K) :
    z ∈ Set.range (branchOpen K s.val) ∨ z ∈ Set.range (punctureOpen K) := by
  rw [show Set.range (branchOpen K s.val) =
    (PrimeSpectrum.basicOpen s.val : Set (PrimeSpectrum K[X])) from
      PrimeSpectrum.localization_away_comap_range (Localization.Away s.val) s.val]
  rw [show Set.range (punctureOpen K) =
    (PrimeSpectrum.basicOpen (X * (X - 1) : K[X]) : Set (PrimeSpectrum K[X])) from
      PrimeSpectrum.localization_away_comap_range (Localization.Away (X * (X - 1) : K[X])) _]
  change s.val ∉ z.asIdeal ∨ X * (X - 1) ∉ z.asIdeal
  by_contra h
  have h' : s.val ∈ z.asIdeal ∧ X * (X - 1) ∈ z.asIdeal := by simpa using h
  have hm := z.asIdeal.mem_of_dvd (conductor_dvd s) h'.2
  rw [hs, C_1] at hm
  exact z.isPrime.one_notMem (by simpa using z.asIdeal.sub_mem h'.1 hm)

/-- Existence of descent from the affine one-gon normalization to arbitrary schemes. -/
theorem exists_desc {Y : Scheme.{u}} (f : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.chartZero K ≫ f = chartOne K ≫ f) :
    ∃ d : Spec (.of (B (R := K))) ⟶ Y, oneBranch K ≫ d = f := by
  obtain ⟨s, hs, d, hd⟩ := exists_local_desc K f w
  let i := neighborhood K s hs
  let j := bPuncture K
  let g := punctureOpen K ≫ f
  have h : pullback.fst i j ≫ d = pullback.snd i j ≫ g :=
    NodePinchingExistence.compatible _ _ _ _ _ _ (isPullback K s hs)
      (puncture_oneBranch K) f d hd
  let e := BinaryOpenDescent.desc (pullback.fst i j) (pullback.snd i j) i j
    (.of_hasPullback i j) (covers K s hs) d g h
  have he₁ : i ≫ e = d := BinaryOpenDescent.inl_desc ..
  have he₂ : j ≫ e = g := BinaryOpenDescent.inr_desc ..
  refine ⟨e, ?_⟩
  apply BinaryOpenDescent.hom_ext (branchOpen K s.val) (punctureOpen K) (line_covers K s hs)
  · rw [← Category.assoc, ← branch_neighborhood, Category.assoc, he₁]
    exact hd
  · simpa only [puncture_oneBranch_assoc] using he₂

/-- A neighborhood of the pinched point contains a normalized principal neighborhood. -/
theorem principal_neighborhood (V : (Spec (.of (B (R := K)))).Opens)
    (hv : bOrigin K (⊥ : PrimeSpectrum K) ∈ V) :
    ∃ s : B (R := K), bEval s = 1 ∧ PrimeSpectrum.basicOpen s ≤ V := by
  obtain ⟨_, ⟨p, rfl⟩, hp, hpV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hv V.isOpen
  have hp' : bEval p ≠ 0 := by
    change bEval p ∉ (⊥ : Ideal K) at hp
    simpa using hp
  refine ⟨algebraMap K _ (bEval p)⁻¹ * p, ?_, ?_⟩
  · simp [hp']
  · exact (PrimeSpectrum.basicOpen_mul_le_right _ _).trans hpV

/-- Arbitrary-target maps from B are determined by their normalization restriction. -/
theorem hom_ext {Y : Scheme.{u}} (d e : Spec (.of (B (R := K))) ⟶ Y)
    (h : oneBranch K ≫ d = oneBranch K ≫ e) : d = e := by
  let o := bOrigin K (⊥ : PrimeSpectrum K)
  have hz : ProjectiveLine.chartZero K ≫ oneBranch K = bOrigin K := by
    rw [ProjectiveLine.chartZero, oneBranch, bOrigin, ← Spec.map_comp]
    rfl
  have ho : d o = e o := by
    have h' := congrArg (fun f ↦ ProjectiveLine.chartZero K ≫ f) h
    simpa only [← Category.assoc, hz, Scheme.Hom.comp_apply, o] using
      congrArg (fun f ↦ f (⊥ : PrimeSpectrum K)) h'
  obtain ⟨U, hU, hoU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := d o) (by trivial)
  obtain ⟨s, hs, hV⟩ := principal_neighborhood K (d ⁻¹ᵁ U ⊓ e ⁻¹ᵁ U)
    (show d o ∈ U ∧ e o ∈ U from ⟨hoU, by rwa [← ho]⟩)
  have hr (a : Spec (.of (B (R := K))) ⟶ Y)
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
  have hb : branch K s hs ≫ d' = branch K s hs ≫ e' := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, Category.assoc, hd', he']
    simp only [branch_neighborhood_assoc, h]
  have w : originZero K s hs ≫ branch K s hs = originOne K s hs ≫ branch K s hs := by
    rw [originZero, branch, originOne, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a ↦ a.property)
  let : IsAffine U := hU
  obtain ⟨_, _, hu⟩ := desc_affine K s hs (branch K s hs ≫ d')
    (by rw [← Category.assoc, ← Category.assoc, w])
  have hde : d' = e' := (hu d' rfl).trans (hu e' hb.symm).symm
  apply BinaryOpenDescent.hom_ext (neighborhood K s hs) (bPuncture K) (covers K s hs)
  · rw [← hd', ← he', hde]
  · rw [← puncture_oneBranch, Category.assoc, Category.assoc, h]

/-- The exact one-gon descent statement, with no affine target hypothesis. -/
theorem oneGon_desc {Y : Scheme.{u}} (f : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.chartZero K ≫ f = chartOne K ≫ f) :
    ∃! d : Spec (.of (B (R := K))) ⟶ Y, oneBranch K ≫ d = f := by
  obtain ⟨d, hd⟩ := exists_desc K f w
  exact ⟨d, hd, fun e he ↦ hom_ext K e d (he.trans hd.symm)⟩

end FLT.Mazur.OneGonPinchingDescent
