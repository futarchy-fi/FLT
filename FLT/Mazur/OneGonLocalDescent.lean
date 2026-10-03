/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonLocalizedEqualizer
public import FLT.Mazur.NodeLocalDescent

/-!
# Descent on a principal neighborhood of the one-gon node

The localized endpoint equalizer supplies affine-target descent and a local
descent near the node for arbitrary target schemes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace FLT.Mazur.OneGonLocalDescent

open PolygonNodePresentation OneGonLocalizedEqualizer PinchingAffineDescent
open NodeLocalDescent (branchOpen)

variable (K : Type u) [Field K] (s : B (R := K)) (hs : bEval s = 1)

/-- The localized normalization mapping to its endpoint equalizer. -/
def branch : Spec (.of (Localization.Away s.val)) ⟶ Spec (.of (E s hs)) :=
  Spec.map (CommRingCat.ofHom (E s hs).subtype)

/-- The zero endpoint on the localized normalization. -/
def originZero : Spec (.of K) ⟶ Spec (.of (Localization.Away s.val)) :=
  Spec.map (CommRingCat.ofHom (evalZero s hs))

/-- The one endpoint on the localized normalization. -/
def originOne : Spec (.of K) ⟶ Spec (.of (Localization.Away s.val)) :=
  Spec.map (CommRingCat.ofHom (evalOne s hs))

/-- The saturated principal neighborhood of the one-gon node. -/
def neighborhood : Spec (.of (E s hs)) ⟶ Spec (.of (B (R := K))) :=
  Spec.map (CommRingCat.ofHom (restriction s hs))

instance : IsOpenImmersion (neighborhood K s hs) := IsOpenImmersion.of_isLocalization s

theorem range_neighborhood : Set.range (neighborhood K s hs) =
    (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum (B (R := K)))) :=
  PrimeSpectrum.localization_away_comap_range (E s hs) s

@[reassoc (attr := simp)]
theorem branch_neighborhood : branch K s hs ≫ neighborhood K s hs =
    branchOpen K s.val ≫ oneBranch K := by
  rw [branch, neighborhood, branchOpen, oneBranch, ← Spec.map_comp, ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem originZero_branchOpen : originZero K s hs ≫ branchOpen K s.val =
    ProjectiveLine.chartZero K := by
  rw [originZero, branchOpen, ProjectiveLine.chartZero, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext
    (NodeLocalizedEqualizer.evaluation_algebraMap _ _ (zero_value s hs)))

@[reassoc (attr := simp)]
theorem originOne_branchOpen : originOne K s hs ≫ branchOpen K s.val = chartOne K := by
  rw [originOne, branchOpen, chartOne, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext
    (NodeLocalizedEqualizer.evaluation_algebraMap _ _ (one_value s hs)))

/-- Localized normalization maps descend uniquely to every affine spectrum. -/
theorem desc_spec {R : CommRingCat.{u}}
    (f : Spec (.of (Localization.Away s.val)) ⟶ Spec R)
    (w : originZero K s hs ≫ f = originOne K s hs ≫ f) :
    ∃! d : Spec (.of (E s hs)) ⟶ Spec R, branch K s hs ≫ d = f := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hw : (evalZero s hs).comp φ.hom = (evalOne s hs).comp φ.hom := by
    rw [originZero, originOne, ← Spec.map_comp, ← Spec.map_comp] at w
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective w)
  let δ : R →+* E s hs := φ.hom.codRestrict (E s hs) (fun r ↦ RingHom.congr_fun hw r)
  refine ⟨Spec.map (CommRingCat.ofHom δ), ?_, ?_⟩
  · dsimp only
    rw [branch, ← Spec.map_comp]; rfl
  · intro d hd
    obtain ⟨ε, rfl⟩ := Spec.map_surjective d
    rw [branch, ← Spec.map_comp] at hd
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun r ↦ Subtype.ext
      (congrArg (fun k ↦ k.hom r) (Spec.map_injective hd)))

/-- Localized normalization maps descend uniquely to every affine target. -/
theorem desc_affine {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (.of (Localization.Away s.val)) ⟶ Y)
    (w : originZero K s hs ≫ f = originOne K s hs ≫ f) :
    ∃! d : Spec (.of (E s hs)) ⟶ Y, branch K s hs ≫ d = f := by
  obtain ⟨d, hd, hu⟩ := desc_spec K s hs (f ≫ Y.isoSpec.hom)
    (by simpa only [← Category.assoc] using congrArg (fun t ↦ t ≫ Y.isoSpec.hom) w)
  refine ⟨d ≫ Y.isoSpec.inv, ?_, ?_⟩
  · dsimp only
    rw [← Category.assoc, hd, Category.assoc, Y.isoSpec.hom_inv_id, Category.comp_id]
  · intro e he
    apply (cancel_mono Y.isoSpec.hom).mp
    simpa using hu (e ≫ Y.isoSpec.hom) (by dsimp only; rw [← Category.assoc, he])

/-- Arbitrary targets admit descent on a saturated neighborhood of the one-gon node. -/
theorem exists_local_desc {Y : Scheme.{u}} (f : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.chartZero K ≫ f = chartOne K ≫ f) :
    ∃ (s : B (R := K)) (hs : bEval s = 1) (d : Spec (.of (E s hs)) ⟶ Y),
      branch K s hs ≫ d = branchOpen K s.val ≫ f := by
  have ho : f (PinchingNeighborhoods.point K 0) = f (PinchingNeighborhoods.point K 1) :=
    congrArg (fun h ↦ h (⊥ : PrimeSpectrum K)) w
  obtain ⟨U, hU, hoU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := f (PinchingNeighborhoods.point K 0)) (by trivial)
  obtain ⟨s, hs, hV⟩ := PinchingNeighborhoods.oneGon_neighborhood K
    (f ⁻¹ᵁ U) hoU (by change f (PinchingNeighborhoods.point K 1) ∈ U; rwa [← ho])
  have hr : Set.range (branchOpen K s.val ≫ f) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hV
    change PrimeSpectrum.comap (algebraMap K[X] (Localization.Away s.val)) z ∈
      (PrimeSpectrum.basicOpen s.val : Set (PrimeSpectrum K[X]))
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away s.val) s.val]
    exact ⟨z, rfl⟩
  let f' := IsOpenImmersion.lift U.ι (branchOpen K s.val ≫ f) hr
  have w' : originZero K s hs ≫ f' = originOne K s hs ≫ f' := by
    apply (cancel_mono U.ι).mp
    simpa [f', Category.assoc, IsOpenImmersion.lift_fac] using w
  let : IsAffine U := hU
  obtain ⟨d, hd, _⟩ := desc_affine K s hs f' w'
  refine ⟨s, hs, d ≫ U.ι, ?_⟩
  rw [← Category.assoc, hd]
  exact IsOpenImmersion.lift_fac _ _ _

/-- The saturated neighborhood and conductor complement cover the one-gon chart. -/
theorem covers (z : Spec (.of (B (R := K)))) :
    z ∈ Set.range (neighborhood K s hs) ∨ z ∈ Set.range (bPuncture K) := by
  by_cases h : z ∈ Set.range (bOrigin K)
  · left
    obtain ⟨q, rfl⟩ := h
    rw [range_neighborhood]
    change bEval s ∉ q.asIdeal
    rw [hs]
    exact q.isPrime.one_notMem
  · right
    rw [range_bPuncture]
    rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    exact (b_zeroLocus_origin K) ▸ h

/-- The localized normalization is the pullback of the saturated neighborhood. -/
theorem isPullback : IsPullback (branchOpen K s.val) (branch K s hs)
    (oneBranch K) (neighborhood K s hs) := by
  let : IsLocalization ((Submonoid.powers s).map (B (R := K)).val.toRingHom)
      (Localization.Away s.val) := by
    rw [Submonoid.map_powers]
    exact inferInstanceAs (IsLocalization.Away s.val (Localization.Away s.val))
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (B (R := K)).val.toRingHom
      (E s hs).subtype (by rfl) (Submonoid.powers s))

end FLT.Mazur.OneGonLocalDescent
