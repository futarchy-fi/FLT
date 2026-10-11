/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothDividedTerminalTensorAction
public import FLT.Mazur.WeierstrassDividedTerminalTensorPointGeometry

/-!
# The genuine terminal output occupies the original cyclic puncture

The constructed integral output, after its actual residue specialization,
is universal scaling on the terminal right puncture with inverse cyclic parameter.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
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
local notation "g" => globalDividedTensorChart hπ data 𝕂 (s + 1) hs
local notation "τ" => smoothHorizontalTangentUnit D
local notation "z" => smoothHorizontalConicUnit D

/-- The actual integral input specializes to the terminal component's right puncture. -/
theorem terminalIntegralTensorInput_cycle :
    Spec.map (CommRingCat.ofHom
        (smoothDividedTerminalTensorInput D d (by omega) (by omega) (by omega)).toRingHom) ≫
        g = Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := 𝕂) z).toRingHom) ≫
          ProjectiveLine.overlapLeft 𝕂 ≫ ProjectiveLine.right 𝕂 ≫
            (Z ⟨s + 2, by omega⟩).left := by
  rw [smoothDividedTerminalTensorInput_eq]
  exact terminalTensorLaurentPoint_cycle hπ data D s hs hstart hk hp z

/-- The actual integral output specializes to universal scaling on that same puncture. -/
theorem terminalIntegralTensorOutput_universal :
    Spec.map (CommRingCat.ofHom
        (smoothDividedTerminalTensorOutput D d (by omega) (by omega) (by omega)).toRingHom) ≫
        g = Spec.map (CommRingCat.ofHom
          (ProjectiveLineUniversalAction.laurentPairEvaluation (K := 𝕂) τ⁻¹ z).toRingHom) ≫
          ProjectiveLineProductOverlap.left 𝕂[T;T⁻¹] ≫
            ProjectiveLineProductCharts.productChartMap 𝕂 𝕂[T;T⁻¹] true ≫
              ProjectiveLineUniversalAction.action 𝕂 ≫ (Z ⟨s + 2, by omega⟩).left := by
  rw [smoothDividedTerminalTensorOutput_eq]
  exact terminalTensorLaurentPoint_universal hπ data D s hs hstart hk hp τ z

end FLT.Mazur.WeierstrassDividedDepth
