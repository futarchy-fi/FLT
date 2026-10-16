/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedEarlierTerminalSeparation
public import FLT.Mazur.TensorOpenChartNilpotentSeparation

/-!
# The complete terminal chart misses earlier charts over nilpotent bases

The entire nonadjacent terminal intersection stays empty at every arithmetic
thickening. The original retained maps and terminal coefficients are preserved.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n)
local notation "E₀" => initialExterior (data (Fin.mk 0 (Nat.zero_lt_succ n)))
local notation "E" => finiteExterior hπ data E₀ j (Nat.le_of_succ_le hj)
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "F" => finiteExterior hπ data E₀ (j + 1) hj
local notation "base" => finiteStructure hπ data (j + 1) hj
local notation "p" => pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S))) base

/-- The full earlier exterior is disjoint from the terminal tensor chart when π is nilpotent. -/
theorem terminalPrecedingTensor_nilpotent_disjoint (hp : IsNilpotent (algebraMap R S π)) :
    Disjoint (Set.range (terminalPrecedingTensorChart hπ data S j hj))
      (Set.range (finiteDividedTensorChart hπ data S (j + 1) hj)) :=
  TensorOpenChart.nilpotent_disjoint base (terminalPrecedingExteriorChart hπ data j hj)
    (F).dividedChart (finiteDivided_structure hπ data (j + 1) hj) π hp
    (terminalPrecedingExterior_parameter_notMem hπ data j hj)

variable [IsBezout R]

/-- Globalization preserves every earlier indexed chart's empty terminal intersection. -/
theorem terminalEarlierGlobalTensor_nilpotent_disjoint
    (hp : IsNilpotent (algebraMap R S π)) (i : Fin (j + 1)) :
    Disjoint (Set.range (globalTensorAtlasMap hπ data S (j + 1) hj i.succ.succ.succ))
      (Set.range (globalDividedTensorChart hπ data S (j + 1) hj)) := by
  have hd := (terminalPrecedingTensor_nilpotent_disjoint hπ data S j hj hp).mono_left
    (terminalEarlierTensorAtlas_range_subset hπ data S j hj i)
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  have he := (finiteLocalTensorEmbedding hπ data S (j + 1) hj).isOpenEmbedding.injective
    (ha.trans hb.symm)
  exact Set.disjoint_left.mp hd ⟨a, rfl⟩ ⟨b, he.symm⟩

/-- Any atlas index beyond the newest exterior is disjoint from the full terminal chart. -/
theorem globalTensorAtlas_terminal_nonadjacent_nilpotent_disjoint
    (m : ℕ) (hm : m ≤ n) (hp : IsNilpotent (algebraMap R S π))
    (i : Fin (m + 3)) (hi : 3 ≤ i.val) :
    Disjoint (Set.range (globalTensorAtlasMap hπ data S m hm i))
      (Set.range (globalDividedTensorChart hπ data S m hm)) := by
  cases m with
  | zero => omega
  | succ j =>
    have he : i = (⟨i.val - 3, by omega⟩ : Fin (j + 1)).succ.succ.succ :=
      Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [he]
    exact terminalEarlierGlobalTensor_nilpotent_disjoint hπ data S j hm hp _

end FLT.Mazur.WeierstrassDividedDepth
