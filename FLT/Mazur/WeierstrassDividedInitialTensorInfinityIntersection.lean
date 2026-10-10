/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialInfinityPreimage
public import FLT.Mazur.WeierstrassDividedInitialGlobalTensorChart
public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# Full initial-chart intersections with infinity after coefficient extension

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
  (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "y" => WeierstrassModificationX.y W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "c" => globalInitialTensorChart hπ data S j hj
local notation "i" => finiteInfinityTensorChart hπ data S j hj
local notation "p" => pullback.snd q (finiteGlobalStructure hπ data j hj)

/-- The whole original initial chart is retained under the global tensor projection. -/
@[reassoc] theorem globalInitialTensorChart_projection :
    c ≫ p = TensorOpenChart.projection ≫ finiteInitialChart hπ data j hj ≫
      finiteLocalChart hπ data j hj := by
  rw [globalInitialTensorChart, Category.assoc, finiteLocalTensorEmbedding_square]
  change TensorOpenChart.chart _ _ _ ≫ _ ≫ _ = _
  rw [TensorOpenChart.chart_snd_assoc]

/-- The full tensor principal open of original y is precisely the infinity preimage. -/
theorem initialGlobalTensor_infinity_preimage :
    c ⁻¹' Set.range i = Set.range (PrincipalOpenTensor.inclusion S y) := by
  rw [finiteInfinityTensorChart_range]
  have he : c ⁻¹' (p ⁻¹' Set.range (finiteInfinityChart hπ data j hj)) =
      TensorOpenChart.projection ⁻¹'
        ((finiteInitialChart hπ data j hj ≫
          finiteLocalChart hπ data j hj) ⁻¹'
            Set.range (finiteInfinityChart hπ data j hj)) := by
    ext z
    change p (c z) ∈ Set.range (finiteInfinityChart hπ data j hj) ↔ _
    have hz : p (c z) = finiteLocalChart hπ data j hj
        (finiteInitialChart hπ data j hj (TensorOpenChart.projection z)) :=
      congrArg (fun f => f z) (globalInitialTensorChart_projection hπ data S j hj)
    rw [hz]
    rfl
  rw [he, finiteInitialChart_infinity_principal]
  change TensorOpenChart.projection ⁻¹' Set.range
    (PrimeSpectrum.comap (algebraMap _ (Localization.Away y))) =
      Set.range (PrimeSpectrum.comap (algebraMap _ (Localization.Away ((1 : S) ⊗ₜ[R] y))))
  rw [PrimeSpectrum.localization_away_comap_range _ y,
    PrimeSpectrum.localization_away_comap_range _ ((1 : S) ⊗ₜ[R] y)]
  rfl

/-- The full original y tensor localization maps canonically to the original infinity chart. -/
def initialGlobalYToInfinity :
    Spec (.of (Localization.Away ((1 : S) ⊗ₜ[R] y))) ⟶
      Spec (.of (S ⊗[R] WeierstrassIntegralChart.Coordinate W 1)) :=
  IsOpenImmersion.lift i (PrincipalOpenTensor.inclusion S y ≫ c) (by
    rintro z ⟨a, rfl⟩
    exact Set.ext_iff.mp (initialGlobalTensor_infinity_preimage hπ data S j hj)
      (PrincipalOpenTensor.inclusion S y a) |>.mpr ⟨a, rfl⟩)

/-- The full infinity attachment retains the actual global inclusions. -/
@[reassoc] theorem initialGlobalYToInfinity_comp :
    initialGlobalYToInfinity hπ data S j hj ≫ i =
      PrincipalOpenTensor.inclusion S y ≫ c :=
  IsOpenImmersion.lift_fac _ _ _

/-- The full original tensor localization is the actual cartesian infinity intersection. -/
theorem initialGlobalTensor_infinity_isPullback :
    IsPullback (initialGlobalYToInfinity hπ data S j hj)
      (PrincipalOpenTensor.inclusion S y) i c := by
  apply IsOpenImmersion.isPullback
  · exact (initialGlobalYToInfinity_comp hπ data S j hj).symm
  · exact TopologicalSpace.Opens.ext (initialGlobalTensor_infinity_preimage hπ data S j hj)

end FLT.Mazur.WeierstrassDividedDepth
