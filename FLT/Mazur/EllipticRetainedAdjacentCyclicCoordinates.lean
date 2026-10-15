/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedHorizontalLineCoordinates
public import FLT.Mazur.WeierstrassDividedAdjacentCyclicTori
public import FLT.Mazur.EllipticRetainedTrivializedCharts
public import FLT.Mazur.LaurentCyclicCoordinateChange

/-!
# Retained arithmetic coordinates in the original adjacent cyclic tori

The full retained charts have the same arbitrary-unit scale corrections as
the terminal charts. No equation on the residue unit is needed here.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FLT.Mazur.PolygonScaledReciprocal

/-- Inverting the source before a scaling gives the same scaled reciprocal substitution. -/
@[reassoc] theorem inversion_spec_scaling {F : Type u} [Field F] (a : Fˣ) :
    (ProjectiveLine.inversion F).hom ≫
      Spec.map (CommRingCat.ofHom (scaling a).toRingHom) =
        Spec.map (CommRingCat.ofHom (reciprocal a).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

end FLT.Mazur.PolygonScaledReciprocal
namespace FLT.Mazur.WeierstrassDividedDepth
variable {K : Type u} [Field K] (A : ValuationSubring K)
  {W : WeierstrassCurve A} {π : A} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (m : ℕ) (hm : j + 2 + m ≤ n)
local notation "F" => ResidueField A
local notation "C" => orderedAdjacentComponent hπ data D j hj hk hjNext hkNext m hm
local notation "pos" => retainedPositiveLaurentChart A hπ data D (j + 1)
  hjNext m hm (by omega) (by omega)
local notation "neg" => retainedNegativeLaurentChart A hπ data D (j + 1)
  hjNext m hm (by omega) (by omega)
local notation "torus" => Over.Hom.left (PolygonPinching.torusToComponent F)

/-- The retained positive puncture is exactly the reversed first cyclic torus. -/
@[reassoc] theorem retainedPositiveLaurentChart_adjacent_cyclic :
    pos = torus ≫ ProjectiveLine.endpointReversal F ≫ C 0 := by
  rw [orderedAdjacentComponent_first_cyclicTorus]
  exact retainedPositiveLaurentChart_line A hπ data D (j + 1) hjNext m hm (by omega) hkNext

/-- The second cyclic torus uses the inverse of the original negative puncture parameter. -/
@[reassoc] theorem adjacent_second_cyclicTorus_retainedNegative :
    torus ≫ C 1 = (ProjectiveLine.inversion F).hom ≫ neg := by
  rw [retainedNegativeLaurentChart_line A hπ data D (j + 1) hjNext m hm (by omega) hkNext,
    PolygonScaledReciprocal.inversion_spec_scaling_assoc,
    orderedAdjacentComponent_second_cyclicTorus]

variable (r : (ResidueField A)ˣ)
local notation "a" => nodeLaurentScale D r (start + (j + 1))

/-- The positive arithmetic trivialization retains its arbitrary residue-unit scaling. -/
@[reassoc] theorem retainedTrivializedPositiveChart_adjacent_cyclic :
    retainedTrivializedPositiveChart A hπ data D r (j + 1) hjNext m hm
        (by omega) (by omega) =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a).toRingHom) ≫
        torus ≫ ProjectiveLine.endpointReversal F ≫ C 0 := by
  rw [retainedTrivializedPositiveChart,
    retainedPositiveLaurentChart_adjacent_cyclic A hπ data D j hj hk hjNext hkNext m hm]

/-- The negative arithmetic trivialization retains the signed inverse residue-unit scaling. -/
@[reassoc] theorem retainedTrivializedNegativeChart_adjacent_cyclic :
    retainedTrivializedNegativeChart A hπ data D r (j + 1) hjNext m hm
        (by omega) (by omega) =
      Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
        torus ≫ C 1 := by
  rw [adjacent_second_cyclicTorus_retainedNegative,
    PolygonScaledReciprocal.inverse_scaling_spec_inversion_assoc]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
