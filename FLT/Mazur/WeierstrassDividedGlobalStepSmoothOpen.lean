/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCenterSmooth
public import FLT.Mazur.WeierstrassDividedGlobalStepExterior
public import FLT.Mazur.WeierstrassDividedGlobalFiniteFlat
public import FLT.Mazur.SchemeUnchangedOpenLift
public import FLT.Mazur.PolygonAtlasSmoothLocus

/-!
# Each global step preserves the preceding model's entire smooth locus

The infinity and exterior charts are unchanged. On the normalized divided
chart the actual center misses its own relative smooth locus, so the full
principal-open pullbacks cover every remaining smooth point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data ⟨j, Nat.lt_succ_of_le (Nat.le_of_succ_le hj)⟩
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "E" => finiteExterior hπ data
  (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j (Nat.le_of_succ_le hj)
local notation "B" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (π * (Data.b3 e)) (π * (Data.b4 e)) (π ^ 2 * (Data.b6 e))
local notation "base" => finiteGlobalStructure hπ data j (Nat.le_of_succ_le hj)

/-- The normalized preceding chart retains its actual divided coefficient structure. -/
@[reassoc] theorem finiteNormalizedChart_structure :
    finiteNormalizedChart hπ data j hj ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [finiteGlobalStructure, finiteNormalizedChart_contraction_assoc,
    integralCurveChart_structure]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (previousOriginalMap hπ d e).comp_algebraMap

/-- Infinity, the preceding exterior and the normalized divided chart cover the target. -/
theorem finitePreceding_charts_cover
    (z : finiteGlobalModel hπ data j (Nat.le_of_succ_le hj)) :
    (∃ p, finiteInfinityChart hπ data j (Nat.le_of_succ_le hj) p = z) ∨
      (∃ p, finitePrecedingExteriorChart hπ data j hj p = z) ∨
        ∃ p, finiteNormalizedChart hπ data j hj p = z := by
  rcases finiteGlobal_charts_cover hπ data j (Nat.le_of_succ_le hj) z with h | ⟨p, hp⟩
  · exact Or.inl h
  rcases (E).charts_cover p with ⟨q, hq⟩ | ⟨q, hq⟩
  · exact Or.inr (Or.inl ⟨q, by
      change finiteLocalChart hπ data j (Nat.le_of_succ_le hj) ((E).exteriorChart q) = z
      rw [hq]
      exact hp⟩)
  · refine Or.inr (Or.inr ⟨(previousChartIso hπ d e).inv q, ?_⟩)
    have he : (previousChartIso hπ d e).hom ((previousChartIso hπ d e).inv q) = q := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    change finiteLocalChart hπ data j (Nat.le_of_succ_le hj)
      ((E).dividedChart ((previousChartIso hπ d e).hom ((previousChartIso hπ d e).inv q))) = z
    rw [he, hq]
    exact hp

variable [IsNoetherianRing R]

/-- The full global successor is unchanged over the preceding relative smooth locus. -/
theorem finiteGlobalStep_smooth_isIso :
    IsIso (finiteGlobalStep hπ data j hj ∣_ (base).smoothLocus) := by
  apply SchemeUnchangedOpen.isIso_of_neighborhoods
  intro z hz
  rcases finitePreceding_charts_cover hπ data j hj z with ⟨p, hp⟩ | ⟨p, hp⟩ | ⟨p, hp⟩
  · refine ⟨(finiteInfinityChart hπ data j (Nat.le_of_succ_le hj)).opensRange,
      ⟨p, hp⟩, ?_⟩
    exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
      (finiteGlobalStep_infinity_isPullback hπ data j hj)
  · refine ⟨(finitePrecedingExteriorChart hπ data j hj).opensRange, ⟨p, hp⟩, ?_⟩
    exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
      (finiteGlobalStep_exterior_isPullback hπ data j hj)
  · have hs := (PolygonAtlas.mem_smooth_iff
        (finiteNormalizedChart hπ data j hj) base p).mp (hp ▸ hz)
    simp only [finiteNormalizedChart_structure] at hs
    have hn := WeierstrassDilatation.successiveCenter_not_le_of_smooth W
      (π ^ (start + j)) (e).b3 (e).b4 (e).b6 π p hs
    change ¬ ∀ f, f ∈ _ → f ∈ p.asIdeal at hn
    push Not at hn
    obtain ⟨f, hf, hfp⟩ := hn
    have hr : p ∈ Set.range (PrincipalAffineRefinement.inclusion f) := by
      rw [PrincipalAffineRefinement.range_inclusion]
      exact hfp
    obtain ⟨q, hq⟩ := hr
    refine ⟨(PrincipalAffineRefinement.inclusion f ≫
      finiteNormalizedChart hπ data j hj).opensRange, ⟨q, ?_⟩, ?_⟩
    · simpa only [Scheme.Hom.comp_apply, hq] using hp
    · exact SchemeUnchangedOpen.isIso_of_identity_pullback _ _ _
        (finiteGlobalStepOriginal_isPullback hπ data j hj f hf)

end FLT.Mazur.WeierstrassDividedDepth
