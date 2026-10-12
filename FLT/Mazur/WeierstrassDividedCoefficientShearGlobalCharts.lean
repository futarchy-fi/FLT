/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCoefficientShearSchemes
public import FLT.Mazur.WeierstrassDividedGlobalTensorCharts
public import FLT.Mazur.WeierstrassDividedInitialGlobalTensorChart
public import FLT.Mazur.SchemeOpenChartRange

/-!
# Actual sheared coefficient charts in the original finite global pullback

The complete sheared divided and initial incidence equations embed into the
original coefficient pullback, with precisely the original tensor-chart ranges.
No domain or Bezout hypothesis is imposed on the extended coefficient ring.
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
  (S : Type u) [CommRing S] [Algebra R S] (r : S) (j : ℕ) (hj : j ≤ n)
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "di" => dividedCoefficientShearIso W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r
local notation "ei" => incidenceCoefficientShearIso W (π ^ start)
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) S r

/-- The whole sheared divided equation embeds in the original global coefficient pullback. -/
def globalDividedCoefficientShearChart :=
  (di).hom ≫ globalDividedTensorChart hπ data S j hj

/-- The whole sheared initial incidence equation embeds in the original coefficient pullback. -/
def globalInitialCoefficientShearChart :=
  (ei).hom ≫ globalInitialTensorChart hπ data S j hj

instance globalDividedCoefficientShearChart_isOpenImmersion :
    IsOpenImmersion (globalDividedCoefficientShearChart hπ data S r j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance globalInitialCoefficientShearChart_isOpenImmersion :
    IsOpenImmersion (globalInitialCoefficientShearChart hπ data S r j hj) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The full original divided tensor chart is retained, including exceptional functions. -/
theorem globalDividedCoefficientShearChart_range :
    Set.range (globalDividedCoefficientShearChart hπ data S r j hj) =
      Set.range (globalDividedTensorChart hπ data S j hj) :=
  SchemeOpenChartRange.range_iso_comp (di) _

/-- The full original incidence tensor chart is retained, including its exceptional conic. -/
theorem globalInitialCoefficientShearChart_range :
    Set.range (globalInitialCoefficientShearChart hπ data S r j hj) =
      Set.range (globalInitialTensorChart hπ data S j hj) :=
  SchemeOpenChartRange.range_iso_comp (ei) _

/-- The divided global chart has its actual extended coefficient structure. -/
@[reassoc] theorem globalDividedCoefficientShearChart_structure :
    globalDividedCoefficientShearChart hπ data S r j hj ≫ pullback.fst q
        (finiteGlobalStructure hπ data j hj) =
      Spec.map (CommRingCat.ofHom (algebraMap S _)) := by
  rw [globalDividedCoefficientShearChart, Category.assoc, globalDividedTensorChart_structure,
    dividedCoefficientShearIso_structure]

/-- The initial global chart has its actual extended coefficient structure. -/
@[reassoc] theorem globalInitialCoefficientShearChart_structure :
    globalInitialCoefficientShearChart hπ data S r j hj ≫ pullback.fst q
        (finiteGlobalStructure hπ data j hj) =
      Spec.map (CommRingCat.ofHom (algebraMap S _)) := by
  rw [globalInitialCoefficientShearChart, Category.assoc, globalInitialTensorChart_structure]
  exact incidenceCoefficientShearIso_structure W (π ^ start)
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) S r

/-- The divided embedding retains the complete original projective contraction and projection. -/
@[reassoc] theorem globalDividedCoefficientShearChart_toCurve :
    globalDividedCoefficientShearChart hπ data S r j hj ≫
        pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
          finiteGlobalContraction hπ data j hj =
      (di).hom ≫ TensorOpenChart.projection ≫ toCurve d := by
  rw [globalDividedCoefficientShearChart, Category.assoc, globalDividedTensorChart_toCurve]

/-- The initial embedding retains the complete original incidence contraction and projection. -/
@[reassoc] theorem globalInitialCoefficientShearChart_toCurve :
    globalInitialCoefficientShearChart hπ data S r j hj ≫
        pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
          finiteGlobalContraction hπ data j hj =
      (ei).hom ≫ TensorOpenChart.projection ≫
        WeierstrassModificationX.toCurve W (π ^ start) (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
          (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀) := by
  rw [globalInitialCoefficientShearChart, Category.assoc, globalInitialTensorChart_toCurve]

end FLT.Mazur.WeierstrassDividedDepth
