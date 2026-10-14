/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteRotatedIdentityClosed

/-!
# Cyclic translates of the identity open cover the original smooth locus

The closed fiber is covered by its original Laurent components. Every other
point already belongs to each translated identity chart. This gives an actual
finite open cover of the unchanged smooth scheme, ready for gluing morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] completePointWeierstrassCurve completePointToIntegralCubic
  exactVeroneseProj exactVeroneseProjToBase
  completeClosedFiberInclusion
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "f" => exactVeroneseProjToBase K n h
local notation "j" => completeClosedFiberInclusion K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
attribute [local instance] exactVeroneseProjToBase_lfp PolygonPinching.cyclic_lfp

/-- Every original closed smooth point belongs to a translated full identity chart. -/
theorem completeRotatedIdentityOpen_closed_cover (x : PolygonCyclicAtlas.scheme K n h)
    (hx : x ∈ (PolygonCyclicAtlas.toBase K n h).smoothLocus) :
    ∃ a : ZMod n, (j) x ∈ completeRotatedIdentityOpen K n h i a := by
  let _ : LocallyOfFinitePresentation (PolygonCyclicAtlas.polygon K n h).hom :=
    PolygonPinching.cyclic_lfp K n h
  have H := Set.ext_iff.mp (smooth_range K n (by omega) p q hp) x
  obtain ⟨k, z, hz⟩ := Set.mem_iUnion.mp (H.mp hx)
  let a := ZMod.finEquiv n k - ZMod.finEquiv n i
  have hk : rotateIndex a i = k := by
    simp [rotateIndex, a]
  refine ⟨a, ?_⟩
  change x ∈ (j) ⁻¹ᵁ completeRotatedIdentityOpen K n h i a
  let _ := torus_isOpenImmersion K n (by omega) p q hp (rotateIndex a i)
  rw [completeRotatedIdentityOpen_closed_preimage]
  exact ⟨z, by simpa only [hk] using hz⟩

/-- The translated identity opens are exactly the entire original smooth locus. -/
theorem completeRotatedIdentityOpen_iSup :
    ⨆ a : ZMod n, completeRotatedIdentityOpen K n h i a = (f).smoothLocus := by
  apply le_antisymm
  · exact iSup_le (completeRotatedIdentityOpen_le_smooth K n h i)
  · intro x hx
    apply TopologicalSpace.Opens.mem_iSup.mpr
    by_cases ht : PowerSeries.X ∈ ((f) x).asIdeal
    · have hb : (f) x = IsLocalRing.closedPoint (PowerSeries K) := by
        apply PrimeSpectrum.ext
        symm
        change IsLocalRing.maximalIdeal (PowerSeries K) = ((f) x).asIdeal
        apply Ideal.IsMaximal.eq_of_le inferInstance ((f) x).isPrime.ne_top
        rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_le_iff_mem]
        exact ht
      have hr : x ∈ Set.range (j) := by
        rw [completeClosedFiber_range]
        exact hb
      obtain ⟨z, rfl⟩ := hr
      exact completeRotatedIdentityOpen_closed_cover K n h i z
        ((completeClosedFiber_mem_smoothLocus K n h z).mp hx)
    · exact ⟨0, completeRotatedIdentityOpen_mem_of_parameter_notMem K n h i 0 x ht⟩

/-- Inclusion of each translated chart in the actual original smooth scheme. -/
def completeRotatedIdentityToSmooth (a : ZMod n) :
    (completeRotatedIdentityOpen K n h i a).toScheme ⟶ (f).smoothLocus.toScheme :=
  (exactVeroneseProj K n h).homOfLE (completeRotatedIdentityOpen_le_smooth K n h i a)

/-- Every chart retains its unchanged original whole-family inclusion. -/
@[reassoc] theorem completeRotatedIdentityToSmooth_inclusion (a : ZMod n) :
    completeRotatedIdentityToSmooth K n h i a ≫ (f).smoothLocus.ι =
      (completeRotatedIdentityOpen K n h i a).ι :=
  Scheme.homOfLE_ι _ _

/-- The actual full smooth polygon is covered by the rotated original identity charts. -/
def completeRotatedIdentityCover : (f).smoothLocus.toScheme.OpenCover where
  I₀ := ZMod n
  X a := (completeRotatedIdentityOpen K n h i a).toScheme
  «f» a := completeRotatedIdentityToSmooth K n h i a
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, ?_⟩
    · have hx : x.1 ∈ ⨆ a : ZMod n, completeRotatedIdentityOpen K n h i a := by
        rw [completeRotatedIdentityOpen_iSup]
        exact x.2
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      refine ⟨a, ⟨x.1, ha⟩, ?_⟩
      apply (f).smoothLocus.ι.isOpenEmbedding.injective
      exact congrArg (fun v ↦ v ⟨x.1, ha⟩)
        (completeRotatedIdentityToSmooth_inclusion K n h i a)
    · intro a
      exact inferInstanceAs (IsOpenImmersion ((exactVeroneseProj K n h).homOfLE
        (completeRotatedIdentityOpen_le_smooth K n h i a)))

end FLT.Mazur.PolygonInfinitesimalStages
