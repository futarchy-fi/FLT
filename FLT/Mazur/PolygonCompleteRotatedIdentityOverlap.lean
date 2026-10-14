/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteRotatedIdentityCover

/-!
# Distinct rotated identity charts meet exactly away from the parameter divisor

Their closed Laurent components are disjoint in the original polygon.
Every nonzero-parameter point belongs to both charts, so the overlap is
exactly the original generic open, with no extra boundary points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] completePointWeierstrassCurve completePointToIntegralCubic
  exactVeroneseProj exactVeroneseProjToBase completeClosedFiberInclusion
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "f" => exactVeroneseProjToBase K n h
local notation "j" => completeClosedFiberInclusion K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "t" k => Over.Hom.left (torusToComponent K ≫ componentι K n k ≫ p)

/-- Distinct original Laurent components have disjoint images in the fixed closed polygon. -/
theorem completeClosedTorus_disjoint {k l : Fin n} (hkl : k ≠ l) :
    Disjoint (Set.range (t k)) (Set.range (t l)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  let e := polygonIso K n (by omega) p q hp
  let _ : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have he₁ := congrArg (fun v ↦ v.left x) (torus_polygonIso K n (by omega) p q hp k)
  have he₂ := congrArg (fun v ↦ v.left y) (torus_polygonIso K n (by omega) p q hp l)
  have he : e.hom.left ((PolygonAtlas.torus K n l).left y) =
      e.hom.left ((PolygonAtlas.torus K n k).left x) := he₂.trans (hy.trans he₁.symm)
  exact Set.disjoint_left.mp (PolygonAtlas.disjoint_torus K n hkl)
    ⟨x, rfl⟩ ⟨y, e.hom.left.isOpenEmbedding.injective he⟩

/-- The original generic open is the inverse image of the nonvanishing parameter locus. -/
def completeParameterOpen : (exactVeroneseProj K n h).Opens :=
  (f) ⁻¹ᵁ PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries K)

/-- Distinct translated identity charts have precisely the original generic open as overlap. -/
theorem completeRotatedIdentityOpen_inf (i : Fin n) (a b : ZMod n) (hab : a ≠ b) :
    completeRotatedIdentityOpen K n h i a ⊓ completeRotatedIdentityOpen K n h i b =
      completeParameterOpen K n h := by
  apply le_antisymm
  · intro x hx
    change PowerSeries.X ∉ ((f) x).asIdeal
    intro ht
    have hb : (f) x = IsLocalRing.closedPoint (PowerSeries K) := by
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
    have ha' := hx.1
    have hb' := hx.2
    change z ∈ (j) ⁻¹ᵁ completeRotatedIdentityOpen K n h i a at ha'
    change z ∈ (j) ⁻¹ᵁ completeRotatedIdentityOpen K n h i b at hb'
    let _ := torus_isOpenImmersion K n (by omega) p q hp (rotateIndex a i)
    let _ := torus_isOpenImmersion K n (by omega) p q hp (rotateIndex b i)
    rw [completeRotatedIdentityOpen_closed_preimage] at ha' hb'
    apply Set.disjoint_left.mp (completeClosedTorus_disjoint K n h ?_) ha' hb'
    intro he
    apply hab
    simpa only [rotateIndex, EquivLike.apply_eq_iff_eq, add_right_inj] using he
  · intro x hx
    exact ⟨completeRotatedIdentityOpen_mem_of_parameter_notMem K n h i a x hx,
      completeRotatedIdentityOpen_mem_of_parameter_notMem K n h i b x hx⟩

end FLT.Mazur.PolygonInfinitesimalStages
