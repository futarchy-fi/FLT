/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalCyclicTori
public import FLT.Mazur.EllipticNodeTrivializedChartGeometry
public import FLT.Mazur.LaurentCyclicCoordinateChange

/-!
# Arithmetic terminal charts in the original cyclic normalization

The positive coordinate differs by the actual tangent scale and the negative
coordinate by its signed inverse. The unit r is arbitrary here: no period
root equation or torsion lifting is assumed in these scheme identities.
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
  (D : SplitNodeDepth W π depth) (r : (ResidueField A)ˣ)
  (s : ℕ) (hs : s + 1 ≤ n) (hstart : start = 0)
  (hp : 2 * (start + s + 1) < depth)
local notation "F" => ResidueField A
local notation "a" => nodeLaurentScale D r (start + (s + 1))
local notation "Z" => zeroSplitCycleComponent hπ data D s hs hstart (by omega) hp

/-- The positive arithmetic torus is the original positive cyclic torus with its actual scale. -/
@[reassoc] theorem nodeTrivializedPositiveChart_cyclic :
    nodeTrivializedPositiveChart A hπ data D r (s + 1) hs (by omega) (by omega) =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a).toRingHom) ≫
        (PolygonPinching.torusToComponent F).left ≫ (Z ⟨s + 1, by omega⟩).left := by
  rw [zeroSplitCycleComponent_terminalPositive_torus]
  rfl

/-- The negative arithmetic torus uses signed inverse scaling in the original cyclic coordinate. -/
@[reassoc] theorem nodeTrivializedNegativeChart_cyclic :
    nodeTrivializedNegativeChart A hπ data D r (s + 1) hs (by omega) (by omega) =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
        (PolygonPinching.torusToComponent F).left ≫ (Z ⟨s + 2, by omega⟩).left := by
  rw [zeroSplitCycleComponent_terminalNegative_torus,
    PolygonScaledReciprocal.inverse_scaling_spec_inversion_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
