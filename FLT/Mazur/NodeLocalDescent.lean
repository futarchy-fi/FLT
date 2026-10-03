/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NodeLocalizedEqualizer
public import FLT.Mazur.NodeSmoothLocus
public import FLT.Mazur.PinchingAffineDescent
public import FLT.Mazur.PinchingNeighborhoods

/-!
# Descent on a principal neighborhood of the node

The localized equalizer gives affine-target descent on a saturated principal
neighborhood. An arbitrary target admits such a neighborhood at the node.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace FLT.Mazur.NodeLocalDescent

open PolygonNodeEqualizer PolygonNodePresentation NodeLocalizedEqualizer

variable (K : Type u) [Field K] (s : A (R := K)) (hs : aEval s = 1)

/-- The first localized normalization branch mapping to the equalizer spectrum. -/
def firstBranch : Spec (.of (Localization.Away (first s))) ⟶ Spec (.of (E s hs)) :=
  Spec.map (CommRingCat.ofHom ((RingHom.fst _ _).comp (E s hs).subtype))

/-- The second localized normalization branch mapping to the equalizer spectrum. -/
def secondBranch : Spec (.of (Localization.Away (second s))) ⟶ Spec (.of (E s hs)) :=
  Spec.map (CommRingCat.ofHom ((RingHom.snd _ _).comp (E s hs).subtype))

/-- The common origin on the first localized branch. -/
def firstOrigin : Spec (.of K) ⟶ Spec (.of (Localization.Away (first s))) :=
  Spec.map (CommRingCat.ofHom (evalFirst s hs))

/-- The common origin on the second localized branch. -/
def secondOrigin : Spec (.of K) ⟶ Spec (.of (Localization.Away (second s))) :=
  Spec.map (CommRingCat.ofHom (evalSecond s hs))

/-- The saturated principal neighborhood of the node. -/
def neighborhood : Spec (.of (E s hs)) ⟶ PolygonNodeBranches.node K :=
  Spec.map (CommRingCat.ofHom (restriction s hs))

instance : IsOpenImmersion (neighborhood K s hs) := IsOpenImmersion.of_isLocalization s

theorem range_neighborhood : Set.range (neighborhood K s hs) =
    (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum (A (R := K)))) :=
  PrimeSpectrum.localization_away_comap_range (E s hs) s

/-- Inclusion of a principal open in the normalization line. -/
def branchOpen (p : K[X]) : Spec (.of (Localization.Away p)) ⟶ ProjectiveLine.chart K :=
  Spec.map (CommRingCat.ofHom (algebraMap K[X] (Localization.Away p)))

@[reassoc (attr := simp)]
theorem firstBranch_neighborhood : firstBranch K s hs ≫ neighborhood K s hs =
    branchOpen K (first s) ≫ PolygonCyclicAtlas.firstBranch K := by
  simp only [firstBranch, neighborhood, branchOpen, PolygonCyclicAtlas.firstBranch,
    ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem secondBranch_neighborhood : secondBranch K s hs ≫ neighborhood K s hs =
    branchOpen K (second s) ≫ PolygonCyclicAtlas.secondBranch K := by
  simp only [secondBranch, neighborhood, branchOpen, PolygonCyclicAtlas.secondBranch,
    ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)]
theorem firstOrigin_branchOpen : firstOrigin K s hs ≫ branchOpen K (first s) =
    ProjectiveLine.chartZero K := by
  rw [firstOrigin, branchOpen, ProjectiveLine.chartZero, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext
    (evaluation_algebraMap _ _ (first_value s hs)))

@[reassoc (attr := simp)]
theorem secondOrigin_branchOpen : secondOrigin K s hs ≫ branchOpen K (second s) =
    ProjectiveLine.chartZero K := by
  rw [secondOrigin, branchOpen, ProjectiveLine.chartZero, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext
    (evaluation_algebraMap _ _ (second_value s hs)))

/-- Localized branch maps descend uniquely to every affine spectrum. -/
theorem desc_spec {R : CommRingCat.{u}}
    (f : Spec (.of (Localization.Away (first s))) ⟶ Spec R)
    (g : Spec (.of (Localization.Away (second s))) ⟶ Spec R)
    (w : firstOrigin K s hs ≫ f = secondOrigin K s hs ≫ g) :
    ∃! d : Spec (.of (E s hs)) ⟶ Spec R,
      firstBranch K s hs ≫ d = f ∧ secondBranch K s hs ≫ d = g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective g
  have hw : (evalFirst s hs).comp φ.hom = (evalSecond s hs).comp ψ.hom := by
    rw [firstOrigin, secondOrigin, ← Spec.map_comp, ← Spec.map_comp] at w
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective w)
  let δ : R →+* E s hs := (φ.hom.prod ψ.hom).codRestrict (E s hs)
    (fun r ↦ RingHom.congr_fun hw r)
  refine ⟨Spec.map (CommRingCat.ofHom δ), ⟨?_, ?_⟩, ?_⟩
  · rw [firstBranch, ← Spec.map_comp]; rfl
  · rw [secondBranch, ← Spec.map_comp]; rfl
  · rintro d ⟨h₁, h₂⟩
    obtain ⟨ε, rfl⟩ := Spec.map_surjective d
    rw [firstBranch, ← Spec.map_comp] at h₁
    rw [secondBranch, ← Spec.map_comp] at h₂
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact Subtype.ext (Prod.ext
      (congrArg (fun k ↦ k.hom r) (Spec.map_injective h₁))
      (congrArg (fun k ↦ k.hom r) (Spec.map_injective h₂)))

/-- Localized branch maps descend uniquely to any affine target. -/
theorem desc_affine {Y : Scheme.{u}} [IsAffine Y]
    (f : Spec (.of (Localization.Away (first s))) ⟶ Y)
    (g : Spec (.of (Localization.Away (second s))) ⟶ Y)
    (w : firstOrigin K s hs ≫ f = secondOrigin K s hs ≫ g) :
    ∃! d : Spec (.of (E s hs)) ⟶ Y,
      firstBranch K s hs ≫ d = f ∧ secondBranch K s hs ≫ d = g := by
  obtain ⟨d, ⟨h₁, h₂⟩, hu⟩ := desc_spec K s hs (f ≫ Y.isoSpec.hom) (g ≫ Y.isoSpec.hom)
    (by simpa only [← Category.assoc] using congrArg (fun t ↦ t ≫ Y.isoSpec.hom) w)
  refine ⟨d ≫ Y.isoSpec.inv, ⟨?_, ?_⟩, ?_⟩
  · rw [← Category.assoc, h₁, Category.assoc, Y.isoSpec.hom_inv_id, Category.comp_id]
  · rw [← Category.assoc, h₂, Category.assoc, Y.isoSpec.hom_inv_id, Category.comp_id]
  · rintro e ⟨he₁, he₂⟩
    apply (cancel_mono Y.isoSpec.hom).mp
    simpa using hu (e ≫ Y.isoSpec.hom) ⟨by rw [← Category.assoc, he₁],
      by rw [← Category.assoc, he₂]⟩

/-- Maps to an arbitrary target descend on some saturated neighborhood of the node. -/
theorem exists_local_desc {Y : Scheme.{u}} (f g : ProjectiveLine.chart K ⟶ Y)
    (w : ProjectiveLine.chartZero K ≫ f = ProjectiveLine.chartZero K ≫ g) :
    ∃ (s : A (R := K)) (hs : aEval s = 1) (d : Spec (.of (E s hs)) ⟶ Y),
      firstBranch K s hs ≫ d = branchOpen K (first s) ≫ f ∧
      secondBranch K s hs ≫ d = branchOpen K (second s) ≫ g := by
  let o := PinchingNeighborhoods.point K 0
  have ho : f o = g o := congrArg (fun h ↦ h (⊥ : PrimeSpectrum K)) w
  obtain ⟨U, hU, hoU, _⟩ := exists_isAffineOpen_mem_and_subset
    (U := ⊤) (x := f o) (by trivial)
  obtain ⟨s, hs, h₁, h₂⟩ := PinchingNeighborhoods.node_neighborhood K
    (f ⁻¹ᵁ U) (g ⁻¹ᵁ U) hoU (by change g o ∈ U; rwa [← ho])
  have hr (p : K[X]) (k : ProjectiveLine.chart K ⟶ Y)
      (h : PrimeSpectrum.basicOpen p ≤ k ⁻¹ᵁ U) :
      Set.range (branchOpen K p ≫ k) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply h
    change PrimeSpectrum.comap (algebraMap K[X] (Localization.Away p)) z ∈
      (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum K[X]))
    rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away p) p]
    exact ⟨z, rfl⟩
  let f' := IsOpenImmersion.lift U.ι (branchOpen K (first s) ≫ f) (hr _ _ h₁)
  let g' := IsOpenImmersion.lift U.ι (branchOpen K (second s) ≫ g) (hr _ _ h₂)
  have w' : firstOrigin K s hs ≫ f' = secondOrigin K s hs ≫ g' := by
    apply (cancel_mono U.ι).mp
    simpa [f', g', Category.assoc, IsOpenImmersion.lift_fac] using w
  let : IsAffine U := hU
  obtain ⟨d, ⟨hd₁, hd₂⟩, _⟩ := desc_affine K s hs f' g' w'
  refine ⟨s, hs, d ≫ U.ι, ?_, ?_⟩
  · rw [← Category.assoc, hd₁]
    exact IsOpenImmersion.lift_fac _ _ _
  · rw [← Category.assoc, hd₂]
    exact IsOpenImmersion.lift_fac _ _ _

/-- The local node neighborhood and the two Laurent branches cover the node chart. -/
theorem covers (z : PolygonNodeBranches.node K) :
    z ∈ Set.range (neighborhood K s hs) ∨
      z ∈ Set.range (PolygonNodeBranches.left K) ∨
      z ∈ Set.range (PolygonNodeBranches.right K) := by
  by_cases h : z ∈ Set.range (aOrigin K)
  · left
    obtain ⟨q, rfl⟩ := h
    rw [range_neighborhood]
    change aEval s ∉ q.asIdeal
    rw [hs]
    exact q.isPrime.one_notMem
  · right
    have hz : z ∈ (Set.range (aOrigin K))ᶜ := h
    rw [← a_zeroLocus_origin, ← PolygonNodeBranches.branches_cover_complement] at hz
    exact hz

/-- The first localized branch is the pullback of the saturated neighborhood. -/
theorem first_isPullback : IsPullback (branchOpen K (first s)) (firstBranch K s hs)
    (PolygonCyclicAtlas.firstBranch K) (neighborhood K s hs) := by
  let : IsLocalization ((Submonoid.powers s).map (first (R := K)).toRingHom)
      (Localization.Away (first s)) := by
    rw [Submonoid.map_powers]
    exact inferInstanceAs (IsLocalization.Away (first s) (Localization.Away (first s)))
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (first (R := K)).toRingHom
      ((RingHom.fst _ _).comp (E s hs).subtype) (by rfl) (Submonoid.powers s))

/-- The second localized branch is the pullback of the saturated neighborhood. -/
theorem second_isPullback : IsPullback (branchOpen K (second s)) (secondBranch K s hs)
    (PolygonCyclicAtlas.secondBranch K) (neighborhood K s hs) := by
  let : IsLocalization ((Submonoid.powers s).map (second (R := K)).toRingHom)
      (Localization.Away (second s)) := by
    rw [Submonoid.map_powers]
    exact inferInstanceAs (IsLocalization.Away (second s) (Localization.Away (second s)))
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (second (R := K)).toRingHom
      ((RingHom.snd _ _).comp (E s hs).subtype) (by rfl) (Submonoid.powers s))

end FLT.Mazur.NodeLocalDescent
