/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveCoefficientShear
public import FLT.Mazur.WeierstrassDividedOlderGlobalTensorCharts
public import FLT.Mazur.SchemeOpenChartRange

/-!
# All retained sheared successive charts in later global coefficient pullbacks

Embed every retained full three-coordinate equation, retaining its range, extended
coefficient map, original cubic contraction, and horizontal zero locus.
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
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
  (t : ℕ) (ht : j + 1 + t ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "ci" => successiveCoefficientShearIso W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) S r

/-- The full sheared successive equation embeds in the original global coefficient pullback. -/
def olderGlobalCoefficientShearChart :=
  (ci).hom ≫ olderGlobalTensorChart hπ data S j hj t ht

instance olderGlobalCoefficientShearChart_isOpenImmersion :
    IsOpenImmersion (olderGlobalCoefficientShearChart hπ data S r j hj t ht) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The actual comparison retains the entire successive tensor chart, also at horizontal zero. -/
theorem olderGlobalCoefficientShearChart_range :
    Set.range (olderGlobalCoefficientShearChart hπ data S r j hj t ht) =
      Set.range (olderGlobalTensorChart hπ data S j hj t ht) :=
  SchemeOpenChartRange.range_iso_comp (ci) _

/-- The whole sheared successive chart has its actual extended coefficient structure. -/
@[reassoc] theorem olderGlobalCoefficientShearChart_structure :
    olderGlobalCoefficientShearChart hπ data S r j hj t ht ≫ pullback.fst q
        (finiteGlobalStructure hπ data (j + 1 + t) ht) =
      Spec.map (CommRingCat.ofHom (algebraMap S _)) := by
  rw [olderGlobalCoefficientShearChart, Category.assoc,
    olderGlobalTensorChart_structure, successiveCoefficientShearIso_structure]

/-- The whole successive chart retains its original projection and cubic contraction. -/
@[reassoc] theorem olderGlobalCoefficientShearChart_toCurve :
    olderGlobalCoefficientShearChart hπ data S r j hj t ht ≫
        pullback.snd q (finiteGlobalStructure hπ data (j + 1 + t) ht) ≫
          finiteGlobalContraction hπ data (j + 1 + t) ht =
      (ci).hom ≫ TensorOpenChart.projection ≫ xContraction hπ d e ≫ toCurve d := by
  rw [olderGlobalCoefficientShearChart, Category.assoc,
    olderGlobalTensorChart_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
