/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootInitialComponents
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentComponentRootChange
import all FLT.Mazur.WeierstrassCoefficientShearRootInitialComponents
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber
import all FLT.Mazur.WeierstrassCoefficientShearRetainedIntersections
import all FLT.Mazur.WeierstrassCoefficientShearRetainedLineRootChange
/-!
# Companion-root exchange on the complete initial projective components

The dense retained-line chart and separatedness identify both independently
glued projective components, including both original affine origins.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (h1 : 1 ≤ n) (m : ℕ) (hm : 1 + m ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
variable (hs : algebraMap R S (π ^ start) = 0) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b3 = 0)
  (h4 : algebraMap R S (data ⟨1, Nat.lt_succ_of_le h1⟩).b4 = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
  (g3 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b3 = 0)
  (g4 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b4 = 0)
  (g6 : algebraMap R S (data ⟨0, Nat.zero_lt_succ n⟩).b6 = 0)
  (a : Sˣ) (ha : (a : S) = (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "U" => rootShearCurve (W.map (algebraMap R S)) r
local notation "c" => algebraMap R S (Data.b6 d)
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "conic" => coefficientShearInitialConic hπ data S r (1 + m) hm hs g3 g4 hr
local notation "E" => conicZeroAffineIso c g6
local notation "F₁" => (E).hom ≫ coefficientConicFirstParameter (U).a₁ c hu conic
local notation "F₂" => (E).hom ≫ coefficientConicSecondParameter (U).a₁ c hu conic
local notation "line" => coefficientShearRetainedLine hπ data S r (1 + m) hm
  (Fin.mk 0 (by omega : 0 < 1 + m)) hs hp h3 h4 hr
local notation "L₁" => line 0 (middle_first_root U)
local notation "L₂" => line (-(U).a₁) (middle_second_root U)
local notation "G" => coefficientShearGluedIso hπ data S r (1 + m) hm

variable (t : S) (b : Sˣ)
  (hb : (b : S) = (rootShearCurve (W.map (algebraMap R S)) t).a₁)
  (ht : t ^ 2 + algebraMap R S W.a₁ * t - algebraMap R S W.a₂ = 0)
  (hrt : r + t = -algebraMap R S W.a₁)
local notation "changeRoot" => coefficientShearRootChange hπ data S r t (1 + m) hm
local notation "gt" => coefficientShearGluedStructure hπ data S t (1 + m) hm
include hrt

/-- Companion-root exchange identifies the complete first initial projective component. -/
@[reassoc] theorem coefficientShearRootInitialFirstComponent_rootChange :
    coefficientShearRootInitialFirstComponent
        hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha ≫ (changeRoot).hom =
      coefficientShearRootInitialSecondComponent
        hπ data S t h1 m hm hs hp h3 h4 ht g3 g4 g6 b hb := by
  let _ : IsSeparated gt := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.rightChart_hom_ext S gt
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearRootInitialFirstComponent_structure,
      coefficientShearRootInitialSecondComponent_structure]
  · rw [coefficientShearRootInitialFirstComponent_right_assoc,
      coefficientShearRootInitialSecondComponent_right,
      coefficientShearRootChange_retainedFirst hπ data S r t (1 + m) 0 hm
        (by omega : 0 < 1 + m) hs hp h3 h4 hr ht hrt]
    rw [coefficientShearAdjacent_oppositeUnits S r a ha t b hb hrt]

/-- Companion-root exchange identifies the complete second initial projective component. -/
@[reassoc] theorem coefficientShearRootInitialSecondComponent_rootChange :
    coefficientShearRootInitialSecondComponent
        hπ data S r h1 m hm hs hp h3 h4 hr g3 g4 g6 a ha ≫ (changeRoot).hom =
      coefficientShearRootInitialFirstComponent
        hπ data S t h1 m hm hs hp h3 h4 ht g3 g4 g6 b hb := by
  let _ : IsSeparated gt := by
    unfold coefficientShearGluedStructure
    infer_instance
  apply ProjectiveLine.rightChart_hom_ext S gt
  · rw [Category.assoc, coefficientShearRootChange_structure,
      coefficientShearRootInitialSecondComponent_structure,
      coefficientShearRootInitialFirstComponent_structure]
  · rw [coefficientShearRootInitialSecondComponent_right_assoc,
      coefficientShearRootInitialFirstComponent_right,
      coefficientShearRootChange_retainedSecond hπ data S r t (1 + m) 0 hm
        (by omega : 0 < 1 + m) hs hp h3 h4 hr ht hrt]
    have hUnits := coefficientShearAdjacent_oppositeUnits S r a ha t b hb hrt
    have hu' : -a = b := by rw [← hUnits, neg_neg]
    rw [hu']

end FLT.Mazur.WeierstrassDividedDepth
