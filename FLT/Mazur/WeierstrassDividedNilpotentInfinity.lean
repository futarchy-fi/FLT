/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderResidueInfinity
public import FLT.Mazur.WeierstrassDividedTensorResidueInfinity

/-!
# Positive-depth full charts miss infinity over every nilpotent base

The original y functions remain nilpotent over arithmetic thickenings.
Thus no point of a full positive-depth retained or terminal chart meets infinity.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {π : R}
  (S : Type u) [CommRing S] [Algebra R S]

/-- The whole original positive-depth y tensor is nilpotent over any nilpotent parameter base. -/
theorem successiveOriginalY_tensor_nilpotent {k : ℕ} (e : Data W π (k + 1))
    (hp : IsNilpotent (algebraMap R S π)) (hk : 0 < k) :
    IsNilpotent ((1 : S) ⊗ₜ[R] successiveOriginalY e) := by
  let T := WeierstrassSuccessiveX.ScalarExtension W (π ^ k) π e.b3 e.b4 e.b6 S
  let f : WeierstrassSuccessiveX.Coordinate W (π ^ k) π e.b3 e.b4 e.b6 →ₐ[R] T :=
    Algebra.TensorProduct.includeRight
  change IsNilpotent (f (successiveOriginalY e))
  rw [successiveOriginalY, map_mul, AlgHom.commutes]
  have hn : IsNilpotent (algebraMap R T (π ^ k)) := by
    rw [IsScalarTower.algebraMap_apply R S T, map_pow]
    exact (hp.pow_of_pos (Nat.ne_of_gt hk)).map (algebraMap S T)
  obtain ⟨N, hN⟩ := hn
  exact ⟨N, by rw [mul_pow, hN, zero_mul]⟩

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
  (hp : IsNilpotent (algebraMap R S π)) (hk : 0 < start + j)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => olderGlobalTensorChart hπ data S j hj r hr
local notation "i" => finiteInfinityTensorChart hπ data S (j + 1 + r) hr

include hp hk in
/-- The entire retained positive-depth chart has empty infinity preimage at every thickening. -/
theorem olderGlobalNilpotent_infinity_preimage : c ⁻¹' Set.range i = ∅ := by
  rw [olderGlobalTensor_infinity_preimage]
  change Set.range (PrimeSpectrum.comap
    (algebraMap _ (Localization.Away ((1 : S) ⊗ₜ[R] successiveOriginalY e)))) = ∅
  rw [PrimeSpectrum.localization_away_comap_range _ ((1 : S) ⊗ₜ[R] successiveOriginalY e)]
  ext z
  change ((1 : S) ⊗ₜ[R] successiveOriginalY e ∉ z.asIdeal) ↔ False
  exact iff_false_intro (not_not_intro ((nilpotent_iff_mem_prime.mp
    (successiveOriginalY_tensor_nilpotent S e hp hk)) z.asIdeal z.isPrime))

include hp hk in
/-- Full retained positive-depth charts are disjoint from the full infinity chart. -/
theorem olderGlobalNilpotent_infinity_disjoint : Disjoint (Set.range c) (Set.range i) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ hx
  exact (Set.ext_iff.mp (olderGlobalNilpotent_infinity_preimage
    S hπ data j hj r hr hp hk) x).mp hx

variable (l : ℕ) (hl : l ≤ n)
local notation "d" => data (Fin.mk l (Nat.lt_succ_of_le hl))
local notation "C" => WeierstrassDilatation.Coordinate W (π ^ (start + l))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ (start + l))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S
local notation "g" => globalDividedTensorChart hπ data S l hl
local notation "i₀" => finiteInfinityTensorChart hπ data S l hl

include hp in
/-- The complete positive-depth terminal chart has empty infinity preimage over nilpotent bases. -/
theorem globalDividedTensor_nilpotent_infinity_preimage (hpos : 0 < start + l) :
    g ⁻¹' Set.range i₀ = ∅ := by
  rw [globalDividedTensor_infinity_preimage]
  let f : C →ₐ[R] T := Algebra.TensorProduct.includeRight
  ext z
  change (f ((WeierstrassDilatation.fromOriginal W (π ^ (start + l))
    (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
    (Data.factor6 d)) (WeierstrassIntegralChart.coord W 2 1))) ∉ z.asIdeal ↔ False
  rw [WeierstrassDilatation.fromOriginal_y, map_mul, AlgHom.commutes]
  have hn : IsNilpotent (algebraMap R T (π ^ (start + l))) := by
    rw [IsScalarTower.algebraMap_apply R S T, map_pow]
    exact (hp.pow_of_pos (Nat.ne_of_gt hpos)).map (algebraMap S T)
  exact iff_false_intro (not_not_intro (z.asIdeal.mul_mem_right _
    ((nilpotent_iff_mem_prime.mp hn) z.asIdeal z.isPrime)))

include hp in
/-- The entire positive-depth terminal chart misses infinity at every arithmetic thickening. -/
theorem globalDividedTensor_nilpotent_infinity_disjoint (hpos : 0 < start + l) :
    Disjoint (Set.range g) (Set.range i₀) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ hx
  exact (Set.ext_iff.mp (globalDividedTensor_nilpotent_infinity_preimage
    S hπ data hp l hl hpos) x).mp hx

end FLT.Mazur.WeierstrassDividedDepth
