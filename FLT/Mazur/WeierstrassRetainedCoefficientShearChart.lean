/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassOlderCoefficientShearGlobalChart
public import FLT.Mazur.WeierstrassDividedAdjacentRetainedTensor

/-!
# Retained coefficient shear charts at a fixed final depth

Every full successive equation embeds at the prescribed final depth over an
arbitrary coefficient algebra. Its range is the original reversed-depth atlas range.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S] (r : S)

/-- The full sheared successive chart with target written as the final depth. -/
def retainedCoefficientShearChart (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t) :=
  olderGlobalCoefficientShearChart hπ data S r j (by omega) (t - (j + 1)) (by omega) ≫
    eqToHom (finiteGlobalTensorModel_index_congr hπ data S (by omega) ht (by omega))

instance retainedCoefficientShearChart_isOpenImmersion
    (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t) :
    IsOpenImmersion (retainedCoefficientShearChart hπ data S r t ht j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Changing only the final depth spelling preserves the complete original sheared chart. -/
theorem retainedCoefficientShearChart_original (j : ℕ) (hj : j + 1 ≤ n)
    (k : ℕ) (hk : j + 1 + k ≤ n) :
    retainedCoefficientShearChart hπ data S r (j + 1 + k) hk j (by omega) =
      olderGlobalCoefficientShearChart hπ data S r j hj k hk := by
  apply eq_of_heq
  refine (comp_eqToHom_heq _ _).trans ?_
  congr 1
  · omega
  · apply proof_irrel_heq

/-- Each retained sheared equation occupies the entire original indexed chart range. -/
theorem retainedCoefficientShearChart_range_index (t : ℕ) (ht : t ≤ n)
    (j : ℕ) (hj : j + 1 ≤ t) :
    Set.range (retainedCoefficientShearChart hπ data S r t ht j hj) =
      Set.range (globalTensorAtlasMap hπ data S t ht ⟨t - j + 1, by omega⟩) := by
  obtain ⟨k, he⟩ : ∃ k, t = j + 1 + k := ⟨t - (j + 1), by omega⟩
  subst t
  rw [retainedCoefficientShearChart_original hπ data S r j (by omega),
    olderGlobalCoefficientShearChart_range]
  have hi : (⟨j + 1 + k - j + 1, by omega⟩ : Fin (j + 1 + k + 3)) =
      Fin.succ ⟨k + 1, by omega⟩ := Fin.ext (by dsimp; omega)
  rw [hi, ← olderGlobalTensorChart_eq_index hπ data S j (by omega) k ht]
  exact SchemeOpenChartRange.range_iso_comp
    (olderSuccessiveTensorAtlasIso hπ data S j (by omega) k ht) _

variable (t : ℕ) (ht : t ≤ n) (j : ℕ) (hj : j + 1 ≤ t)
local notation "d" => data (Fin.mk j (by omega))
local notation "e" => data (Fin.mk (j + 1) (by omega))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "ci" => successiveCoefficientShearIso W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) S r

/-- The transported full chart still has its actual extended coefficient structure. -/
@[reassoc] theorem retainedCoefficientShearChart_structure :
    retainedCoefficientShearChart hπ data S r t ht j hj ≫
        pullback.fst q (finiteGlobalStructure hπ data t ht) =
      Spec.map (CommRingCat.ofHom (algebraMap S _)) := by
  obtain ⟨k, he⟩ : ∃ k, t = j + 1 + k := ⟨t - (j + 1), by omega⟩
  subst t
  rw [retainedCoefficientShearChart_original hπ data S r j (by omega)]
  exact olderGlobalCoefficientShearChart_structure hπ data S r j (by omega) k ht

/-- The fixed-depth embedding retains the original projection on every function. -/
@[reassoc] theorem retainedCoefficientShearChart_toCurve :
    retainedCoefficientShearChart hπ data S r t ht j hj ≫
        pullback.snd q (finiteGlobalStructure hπ data t ht) ≫
          finiteGlobalContraction hπ data t ht =
      (ci).hom ≫ TensorOpenChart.projection ≫ xContraction hπ d e ≫ toCurve d := by
  obtain ⟨k, he⟩ : ∃ k, t = j + 1 + k := ⟨t - (j + 1), by omega⟩
  subst t
  rw [retainedCoefficientShearChart_original hπ data S r j (by omega)]
  exact olderGlobalCoefficientShearChart_toCurve hπ data S r j (by omega) k ht

end FLT.Mazur.WeierstrassDividedDepth
