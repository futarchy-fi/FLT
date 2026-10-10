/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderInfinityPreimage
public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# Full infinity intersections in the retained global tensor atlas

The exact original y principal localization is the entire cartesian
intersection with infinity at every later stage. Its scale is retained
under arbitrary coefficient extension, even when it vanishes on a fiber.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "y" => successiveOriginalY e
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "c" => olderGlobalTensorChart hπ data S j hj r hr
local notation "i" => finiteInfinityTensorChart hπ data S (j + 1 + r) hr
local notation "p" => pullback.snd q (finiteGlobalStructure hπ data (j + 1 + r) hr)

/-- The whole original older chart is retained under the global tensor projection. -/
@[reassoc] theorem olderGlobalTensorChart_projection :
    c ≫ p = TensorOpenChart.projection ≫ olderSuccessiveChart hπ data j hj r hr ≫
      finiteLocalChart hπ data (j + 1 + r) hr := by
  rw [olderGlobalTensorChart, Category.assoc, finiteLocalTensorEmbedding_square]
  change TensorOpenChart.chart _ _ _ ≫ _ ≫ _ = _
  rw [TensorOpenChart.chart_snd_assoc]

/-- The full tensor principal open of original y is precisely the infinity preimage. -/
theorem olderGlobalTensor_infinity_preimage :
    c ⁻¹' Set.range i = Set.range (PrincipalOpenTensor.inclusion S y) := by
  rw [finiteInfinityTensorChart_range]
  have he : c ⁻¹' (p ⁻¹' Set.range (finiteInfinityChart hπ data (j + 1 + r) hr)) =
      TensorOpenChart.projection ⁻¹'
        ((olderSuccessiveChart hπ data j hj r hr ≫
          finiteLocalChart hπ data (j + 1 + r) hr) ⁻¹'
            Set.range (finiteInfinityChart hπ data (j + 1 + r) hr)) := by
    ext z
    change p (c z) ∈ Set.range (finiteInfinityChart hπ data (j + 1 + r) hr) ↔ _
    have hz : p (c z) = finiteLocalChart hπ data (j + 1 + r) hr
        (olderSuccessiveChart hπ data j hj r hr (TensorOpenChart.projection z)) :=
      congrArg (fun f => f z) (olderGlobalTensorChart_projection hπ data S j hj r hr)
    rw [hz]
    rfl
  rw [he, olderSuccessiveChart_infinity_principal]
  change TensorOpenChart.projection ⁻¹' Set.range
    (PrimeSpectrum.comap (algebraMap _ (Localization.Away y))) =
      Set.range (PrimeSpectrum.comap (algebraMap _ (Localization.Away ((1 : S) ⊗ₜ[R] y))))
  rw [PrimeSpectrum.localization_away_comap_range _ y,
    PrimeSpectrum.localization_away_comap_range _ ((1 : S) ⊗ₜ[R] y)]
  rfl

/-- The full original y tensor localization maps canonically to the original infinity chart. -/
def olderGlobalYToInfinity :
    Spec (.of (Localization.Away ((1 : S) ⊗ₜ[R] y))) ⟶
      Spec (.of (S ⊗[R] WeierstrassIntegralChart.Coordinate W 1)) :=
  IsOpenImmersion.lift i (PrincipalOpenTensor.inclusion S y ≫ c) (by
    rintro z ⟨a, rfl⟩
    exact Set.ext_iff.mp (olderGlobalTensor_infinity_preimage hπ data S j hj r hr)
      (PrincipalOpenTensor.inclusion S y a) |>.mpr ⟨a, rfl⟩)

/-- The full infinity attachment retains the actual global inclusions. -/
@[reassoc] theorem olderGlobalYToInfinity_comp :
    olderGlobalYToInfinity hπ data S j hj r hr ≫ i =
      PrincipalOpenTensor.inclusion S y ≫ c :=
  IsOpenImmersion.lift_fac _ _ _

/-- The full original tensor localization is the actual cartesian infinity intersection. -/
theorem olderGlobalTensor_infinity_isPullback :
    IsPullback (olderGlobalYToInfinity hπ data S j hj r hr)
      (PrincipalOpenTensor.inclusion S y) i c := by
  apply IsOpenImmersion.isPullback
  · exact (olderGlobalYToInfinity_comp hπ data S j hj r hr).symm
  · exact TopologicalSpace.Opens.ext (olderGlobalTensor_infinity_preimage hπ data S j hj r hr)

end FLT.Mazur.WeierstrassDividedDepth
