/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalComponents
public import FLT.Mazur.WeierstrassCoefficientShearTerminalBranchRootChange
public import FLT.Mazur.ProjectiveLineRightChartExt
public import FLT.Mazur.WeierstrassDividedGlobalFiniteProper
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Companion-root exchange of complete terminal projective components

The full terminal branch comparison extends across each independently glued
projective line by separatedness, preserving the actual terminal indices.
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
variable (hs : algebraMap R S (π ^ (start + j)) = 0)
  (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b4 = 0)
  (h6 : algebraMap R S (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "hsNext" => show algebraMap R S (π ^ (start + (j + 1))) = 0 from by
  rw [← Nat.add_assoc, pow_succ, map_mul, hp, mul_zero]
variable (t : S)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (b : Sˣ) (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (hrt : r + t = -algebraMap R S W.a₁)
local notation "C" => coefficientShearRootChange hπ data S r t (j + 1) hj
local notation "G" => coefficientShearGluedIso hπ data S t (j + 1) hj
include hrt

local notation "base" => coefficientShearGluedStructure hπ data S t (j + 1) hj

/-- Companion-root exchange identifies the complete first terminal projective component. -/
@[reassoc] theorem coefficientShearRootTerminalFirstComponent_rootChange :
    coefficientShearRootTerminalFirstComponent
        hπ data S r j hj hs hp h3 h4 h6 hr a ha ≫ (C).hom =
      coefficientShearRootTerminalSecondComponent
        hπ data S t j hj hs hp h3 h4 h6 ht b hb := by
  let _ : IsSeparated base := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.rightChart_hom_ext S base
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearRootTerminalFirstComponent_structure,
      coefficientShearRootTerminalSecondComponent_structure]
  · rw [coefficientShearRootTerminalFirstComponent_right_assoc,
      coefficientShearRootTerminalSecondComponent_right]
    exact coefficientShearRootChange_terminalSecond
      hπ data S r j hj hp h3 h4 h6 hr a ha t ht b hb hrt

/-- Companion-root exchange identifies the complete second terminal projective component. -/
@[reassoc] theorem coefficientShearRootTerminalSecondComponent_rootChange :
    coefficientShearRootTerminalSecondComponent
        hπ data S r j hj hs hp h3 h4 h6 hr a ha ≫ (C).hom =
      coefficientShearRootTerminalFirstComponent
        hπ data S t j hj hs hp h3 h4 h6 ht b hb := by
  let _ : IsSeparated base := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.rightChart_hom_ext S base
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearRootTerminalSecondComponent_structure,
      coefficientShearRootTerminalFirstComponent_structure]
  · rw [coefficientShearRootTerminalSecondComponent_right_assoc,
      coefficientShearRootTerminalFirstComponent_right]
    exact coefficientShearRootChange_terminalFirst
      hπ data S r j hj hp h3 h4 h6 hr a ha t ht b hb hrt

end FLT.Mazur.WeierstrassDividedDepth
