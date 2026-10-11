/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationLaurentPointCharacters
public import FLT.Mazur.WeierstrassDividedPositiveEqualityCycleEndCharts
public import FLT.Mazur.ProjectiveLineUniversalLaurentEvaluation

/-!
# Terminal Laurent points keep the reversed cyclic orientation

The original divided vertical coordinate is the right projective coordinate
of the terminal component. Its positive character is the inverse cyclic group unit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "𝕂" => ResidueField R
local notation "d" => data (Fin.mk (s + 1) (Nat.lt_succ_of_le hs))
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "t" => terminalLaurentChart hπ data D (s + 1) hs (by omega) hk hp
local notation "g" => globalDividedTensorChart hπ data 𝕂 (s + 1) hs
variable {C : Type u} [CommRing C] [Algebra (ResidueField R) C]
local notation "point" => terminalTensorLaurentPoint D (start + (s + 1)) (by omega)
  (by omega) (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (by omega) (C := C)

/-- Every terminal tensor point is the same actual Laurent chart point. -/
theorem terminalTensorLaurentPoint_chart (q : Cˣ) :
    Spec.map (CommRingCat.ofHom (point q).toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := 𝕂) q).toRingHom) ≫ t := by
  rw [terminalTensorLaurentPoint, lineSpec_comp]
  rfl

/-- The original terminal vertical parameter is the right cyclic puncture. -/
theorem terminalTensorLaurentPoint_cycle (q : Cˣ) :
    Spec.map (CommRingCat.ofHom (point q).toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := 𝕂) q).toRingHom) ≫
        ProjectiveLine.overlapLeft 𝕂 ≫ ProjectiveLine.right 𝕂 ≫
          (Z ⟨s + 2, by omega⟩).left := by
  rw [terminalTensorLaurentPoint_chart hπ data D s hs hstart hk hp]
  rw [← positiveEqualityCycleComponent_terminal_chart hπ data D s hs hstart hk hp]
  simp only [ProjectiveLine.endpointReversalIso, ProjectiveLine.left_endpointReversal_assoc]

/-- The positive terminal character agrees with inverse-parameter universal cyclic scaling. -/
theorem terminalTensorLaurentPoint_universal (τ q : Cˣ) :
    Spec.map (CommRingCat.ofHom (point (τ * q)).toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom
        (ProjectiveLineUniversalAction.laurentPairEvaluation (K := 𝕂) τ⁻¹ q).toRingHom) ≫
        ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
          ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] true ≫
            ProjectiveLineUniversalAction.action 𝕂 ≫ (Z ⟨s + 2, by omega⟩).left := by
  rw [terminalTensorLaurentPoint_cycle hπ data D s hs hstart hk hp]
  have h := congrArg (· ≫ (Z ⟨s + 2, by omega⟩).left)
    (ProjectiveLineUniversalAction.laurentPairEvaluation_right_action (K := 𝕂) τ⁻¹ q)
  simp only [inv_inv, Category.assoc] at h
  exact h.symm

end FLT.Mazur.WeierstrassDividedDepth
