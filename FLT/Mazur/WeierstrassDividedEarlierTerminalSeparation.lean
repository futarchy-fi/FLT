/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedExteriorTerminalSupport
public import FLT.Mazur.WeierstrassDividedGlobalTensorAtlas
public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts
public import FLT.Mazur.TensorOpenChartVanishingSeparation

/-!
# The terminal tensor chart misses all nonadjacent exterior charts

The whole preceding exterior meets the new divided chart only where π is nonzero.
This excludes every earlier indexed atlas member after coefficient extension killing π.
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

/-- The entire preceding exterior in the final whole integral scheme. -/
def terminalPrecedingExteriorChart : (E).carrier ⟶ finiteModification hπ data (j + 1) hj :=
  (E).retained hπ e ≫ (F).exteriorChart

/-- The newest integral chart retains its coefficient structure before terminal exclusion. -/
@[reassoc] theorem terminalNewX_structure :
    (E).newX hπ e ≫ (F).exteriorChart ≫ base =
      Spec.map (CommRingCat.ofHom (algebraMap R
        (WeierstrassSuccessiveX.Coordinate W (π ^ (start + j)) π
          (Data.b3 e) (Data.b4 e) (Data.b6 e)))) := by
  change finiteExteriorAtlasMap hπ data E₀ (j + 1) hj 0 ≫
    (F).exteriorChart ≫ base = _
  rw [finiteStructure, finiteExteriorAtlas_new_toCurve_assoc, xContraction_structure]

/-- An integral intersection of the preceding exterior with the terminal chart avoids π. -/
theorem terminalPrecedingExterior_parameter_notMem (a : (E).carrier) (c : chart e)
    (h : terminalPrecedingExteriorChart hπ data j hj a = (F).dividedChart c) :
    π ∉ (base ((F).dividedChart c)).asIdeal := by
  exact (E).retained_divided_parameter_notMem hπ e base
    (terminalNewX_structure hπ data j hj) a c h

/-- The preceding exterior's actual coefficient pullback. -/
def terminalPrecedingTensorChart := pullback.snd (terminalPrecedingExteriorChart hπ data j hj) p

/-- The full earlier exterior is disjoint from the terminal tensor chart when π vanishes. -/
theorem terminalPrecedingTensor_disjoint (hp : algebraMap R S π = 0) :
    Disjoint (Set.range (terminalPrecedingTensorChart hπ data S j hj))
      (Set.range (finiteDividedTensorChart hπ data S (j + 1) hj)) :=
  TensorOpenChart.vanishing_disjoint base (terminalPrecedingExteriorChart hπ data j hj)
    (F).dividedChart (finiteDivided_structure hπ data (j + 1) hj) π hp
    (terminalPrecedingExterior_parameter_notMem hπ data j hj)

/-- Every nonadjacent finite tensor member lies in the full preceding exterior. -/
theorem terminalEarlierTensorAtlas_range_subset (i : Fin (j + 1)) :
    Set.range (finiteTensorAtlasMap hπ data S (j + 1) hj i.succ.succ) ⊆
      Set.range (terminalPrecedingTensorChart hπ data S j hj) := by
  rintro z ⟨a, rfl⟩
  have H := finiteTensorAtlasMap_isPullback hπ data S (j + 1) hj i.succ.succ
  have hi : Set.range (finiteAtlasMap hπ data E₀ (j + 1) hj i.succ.succ) ⊆
      Set.range (terminalPrecedingExteriorChart hπ data j hj) := by
    rintro z ⟨b, rfl⟩
    exact ⟨finiteExteriorAtlasMap hπ data E₀ j (Nat.le_of_succ_le hj) i b, rfl⟩
  obtain ⟨b, hb⟩ := hi
    (show p (finiteTensorAtlasMap hπ data S (j + 1) hj i.succ.succ a) ∈
      Set.range (finiteAtlasMap hπ data E₀ (j + 1) hj i.succ.succ) from
        ⟨_, (congrArg (fun f => f a) H.w).symm⟩)
  obtain ⟨c, _, hc⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback (terminalPrecedingExteriorChart hπ data j hj) p) b _ hb
  exact ⟨c, hc⟩

variable [IsBezout R]

/-- Globalization preserves every earlier indexed chart's empty terminal intersection. -/
theorem terminalEarlierGlobalTensor_disjoint (hp : algebraMap R S π = 0) (i : Fin (j + 1)) :
    Disjoint (Set.range (globalTensorAtlasMap hπ data S (j + 1) hj i.succ.succ.succ))
      (Set.range (globalDividedTensorChart hπ data S (j + 1) hj)) := by
  have hd := (terminalPrecedingTensor_disjoint hπ data S j hj hp).mono_left
    (terminalEarlierTensorAtlas_range_subset hπ data S j hj i)
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  have he := (finiteLocalTensorEmbedding hπ data S (j + 1) hj).isOpenEmbedding.injective
    (ha.trans hb.symm)
  exact Set.disjoint_left.mp hd ⟨a, rfl⟩ ⟨b, he.symm⟩

/-- Any atlas index beyond the newest exterior is disjoint from the full terminal chart. -/
theorem globalTensorAtlas_terminal_nonadjacent_disjoint
    (m : ℕ) (hm : m ≤ n) (hp : algebraMap R S π = 0)
    (i : Fin (m + 3)) (hi : 3 ≤ i.val) :
    Disjoint (Set.range (globalTensorAtlasMap hπ data S m hm i))
      (Set.range (globalDividedTensorChart hπ data S m hm)) := by
  cases m with
  | zero => omega
  | succ j =>
    have he : i = (⟨i.val - 3, by omega⟩ : Fin (j + 1)).succ.succ.succ :=
      Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [he]
    exact terminalEarlierGlobalTensor_disjoint hπ data S j hm hp _

end FLT.Mazur.WeierstrassDividedDepth
