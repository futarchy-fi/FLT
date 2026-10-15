/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroEqualityCycle
public import FLT.Mazur.EllipticNodeTrivializedChartGeometry
public import FLT.Mazur.LaurentCyclicCoordinateChange
public import FLT.Mazur.PolygonAtlasSmoothLocus

/-!
# The even middle arithmetic coordinate in the original complete cycle

The reversed complete middle component has reciprocal Laurent coordinate.
The arithmetic chart is its signed inverse scaling, including depth two.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : start = 0) (hp : 2 * (start + s + 1) = depth)
local notation "F" => ResidueField A
local notation "Z" => zeroEqualityCycleComponent hπ data D s hs hstart (by omega) hp

/-- Reversing the complete middle component inverts its original Laurent coordinate. -/
@[reassoc] theorem zeroEqualityCycleComponent_middle_torus :
    (PolygonPinching.torusToComponent F).left ≫ (Z ⟨s + 1, by omega⟩).left =
      (ProjectiveLine.inversion F).hom ≫
        terminalLaurentChart hπ data D (s + 1) hs (by omega) (by omega) (by omega) := by
  rw [zeroEqualityCycleComponent_terminal]
  change (ProjectiveLine.overlapLeft F ≫ ProjectiveLine.left F) ≫
    ProjectiveLine.endpointReversal F ≫
      laurentTerminalProjectiveComponent hπ data D s hs (by omega) hp = _
  rw [Category.assoc, ProjectiveLine.left_endpointReversal_assoc,
    ← Category.assoc, ProjectiveLine.endpointReversal_overlap,
    ProjectiveLine.overlapRight, Category.assoc, Category.assoc,
    laurentTerminalProjectiveComponent_torus]

/-- The actual even arithmetic torus is inverse scaling of the complete cyclic middle torus. -/
@[reassoc] theorem nodeTrivializedMiddleChart_cyclic (r : (ResidueField A)ˣ) :
    nodeTrivializedMiddleChart A hπ data D r (s + 1) hs (by omega) (by omega) =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling
        (-nodeLaurentScale D r (start + (s + 1)))⁻¹).toRingHom) ≫
          (PolygonPinching.torusToComponent F).left ≫ (Z ⟨s + 1, by omega⟩).left := by
  rw [zeroEqualityCycleComponent_middle_torus,
    PolygonScaledReciprocal.inverse_scaling_spec_inversion_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
