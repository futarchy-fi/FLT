/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootLaurentOverlap
public import FLT.Mazur.WeierstrassSuccessiveShearTerminalLaurentCoefficient
public import FLT.Mazur.WeierstrassDividedTensorPointAction

/-!
# Integral projection of the entire terminal Laurent chart

The normalized terminal Laurent chart retains the original unsheared tensor and
integral coordinate maps through the actual final divided chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S) (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
variable (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (hc : IsUnit (algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6))
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
local notation "G" => coefficientShearGluedIso hπ data S r (j + 1) hj
local notation "P" => coefficientShearGluedProjection hπ data S r (j + 1) hj
local notation "F" => finiteDividedGlobalChart hπ data (j + 1) hj

local notation "N" => coefficientShearTerminalLaurent
  hπ data S r (j + 1) hj hsNext h3 h4 hc hr a ha
local notation "I" => originalShearTerminalLaurentMap W π (start + j)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hp h3 h4 hr hc a ha

/-- The complete Laurent chart projects through every original integral divided function. -/
@[reassoc] theorem coefficientShearTerminalLaurent_projection :
    N ≫ P = Spec.map (CommRingCat.ofHom (I).toRingHom) ≫ F := by
  rw [coefficientShearGluedProjection,
    coefficientShearRootTerminalLaurent_reconstruction_assoc (hp := hp),
    globalDividedTensorChart_integralProjection, ← Category.assoc]
  apply congrArg (· ≫ F)
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
