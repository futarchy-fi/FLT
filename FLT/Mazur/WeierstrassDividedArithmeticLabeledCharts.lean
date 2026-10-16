/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticAtlasCoverage
public import FLT.Mazur.WeierstrassModificationXArithmeticTensorNodes
public import FLT.Mazur.WeierstrassDilatationArithmeticTerminalNode
public import FLT.Mazur.WeierstrassSuccessiveArithmeticTensorCoverage

/-!
# The labeled arithmetic charts with their actual original maps

The coefficient conditions below concern only the original integral equations.
The full initial neighborhoods, all labeled retained nodes, the normalized
terminal node, and the original infinity chart are constructed explicitly.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] {W : WeierstrassCurve R} {π : R} {start n : ℕ}

/-- Integral coefficient conditions for constructing every labeled arithmetic chart. -/
structure ArithmeticAtlasCoefficients
    (data : (i : Fin (n + 1)) → Data W π (start + i.val)) : Prop where
  a1_unit : IsUnit W.a₁
  scale_div : π ∣ π ^ start
  a2_div : π ∣ W.a₂
  b3_div : ∀ i, π ∣ (data i).b3
  b4_div : ∀ i, π ∣ (data i).b4
  b6_div : ∀ i, π ∣ (data i).b6

/-- Initial scale divisibility propagates to every retained depth. -/
theorem ArithmeticAtlasCoefficients.scale
    {data : (i : Fin (n + 1)) → Data W π (start + i.val)}
    (H : ArithmeticAtlasCoefficients data) (a : ℕ) : π ∣ π ^ (start + a) := by
  rw [pow_add]
  exact dvd_mul_of_dvd_left H.scale_div _

variable [IsDomain R] [IsBezout R] (hπ : π ≠ 0)
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (k : ℕ) (hk : k ≤ n)
local notation "Q" => Quotient R π m
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "dₖ" => data (Fin.mk k (Nat.lt_succ_of_le hk))

/-- Both full initial nodes, labeled by their original small and opposite roots. -/
def arithmeticLabeledInitialChart (label : Bool) :=
  (if label then arithmeticOppositeInitialTensorNodeChart π m W (π ^ start)
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)
  else arithmeticInitialTensorNodeChart π m W (π ^ start)
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _)) ≫
    finiteArithmeticInitialTensorChart hπ data m k hk

/-- Each labeled retained node has its original depth and a map to the same arithmetic stage. -/
def arithmeticLabeledRetainedChart (a : Fin k) (label : Bool) :=
  arithmeticTensorBranchChart π m W (π ^ (start + a.val))
    (data ⟨a.val + 1, by omega⟩).b3 (data ⟨a.val + 1, by omega⟩).b4
    (data ⟨a.val + 1, by omega⟩).b6 H.a1_unit (H.scale a.val) H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) label ≫
        arithmeticRetainedTensorChart hπ data m k hk a.val a.isLt

/-- The entire normalized terminal node in the original arithmetic stage. -/
def arithmeticLabeledTerminalChart :=
  (WeierstrassDilatation.arithmeticTerminalNodeIso π m W (π ^ (start + k))
    (Data.b3 dₖ) (Data.b4 dₖ) (Data.b6 dₖ) H.a1_unit (H.scale k) H.a2_div
      (H.b4_div _) (H.b6_div _)).hom ≫
        finiteArithmeticDividedTensorChart hπ data m k hk

instance arithmeticLabeledInitialChart_isOpenImmersion (label : Bool) :
    IsOpenImmersion (arithmeticLabeledInitialChart hπ data H m k hk label) := by
  let _ := finiteArithmeticInitialTensorChart_isOpenImmersion hπ data m k hk
  unfold arithmeticLabeledInitialChart
  cases label <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · let _ := arithmeticInitialTensorNodeChart_isOpenImmersion π m W (π ^ start)
      (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _)
    exact IsOpenImmersion.comp _ _
  · let _ := arithmeticOppositeInitialTensorNodeChart_isOpenImmersion π m W (π ^ start)
      (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) H.a1_unit H.a2_div
        (H.b3_div _) (H.b4_div _) (H.b6_div _)
    exact IsOpenImmersion.comp _ _

instance arithmeticLabeledRetainedChart_isOpenImmersion (a : Fin k) (label : Bool) :
    IsOpenImmersion (arithmeticLabeledRetainedChart hπ data H m k hk a label) := by
  let _ := arithmeticTensorBranchChart_isOpenImmersion π m W (π ^ (start + a.val))
    (data ⟨a.val + 1, by omega⟩).b3 (data ⟨a.val + 1, by omega⟩).b4
    (data ⟨a.val + 1, by omega⟩).b6 H.a1_unit (H.scale a.val) H.a2_div
      (H.b3_div _) (H.b4_div _) (H.b6_div _) label
  unfold arithmeticLabeledRetainedChart
  exact IsOpenImmersion.comp _ _

instance arithmeticLabeledTerminalChart_isOpenImmersion :
    IsOpenImmersion (arithmeticLabeledTerminalChart hπ data H m k hk) := by
  let _ := finiteArithmeticDividedTensorChart_isOpenImmersion hπ data m k hk
  unfold arithmeticLabeledTerminalChart
  infer_instance

end FLT.Mazur.WeierstrassDividedDepth
