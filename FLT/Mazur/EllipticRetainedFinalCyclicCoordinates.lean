/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticRetainedAdjacentCyclicCoordinates
public import FLT.Mazur.WeierstrassDividedZeroSplitCycle
public import FLT.Mazur.WeierstrassDividedZeroEqualityCycle

/-!
# Retained arithmetic coordinates in the final odd and even component cycles

Stage transport preserves the full retained charts. The actual odd and even
cycle lists retain the positive scale and signed negative inverse scale.
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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + s + 1) ≤ depth) (j : Fin s)
local notation "F" => ResidueField A
local notation "m" => s - (j.val + 1)
local notation "t" => eqToHom (finiteGlobalTensorModel_index_congr hπ data F
  (a := j.val + 2 + m) (by omega) hs (by omega))
local notation "a" => nodeLaurentScale D r (start + (j.val + 1))
local notation "pos" => retainedTrivializedPositiveChart A hπ data D r (j.val + 1)
  (by omega) m (by omega) (by omega) (by omega)
local notation "neg" => retainedTrivializedNegativeChart A hπ data D r (j.val + 1)
  (by omega) m (by omega) (by omega) (by omega)
local notation "torus" => Over.Hom.left (PolygonPinching.torusToComponent F)
local notation "C" => finalAdjacentComponent hπ data D s hs hk j

/-- Final-stage index transport retains the entire positive arithmetic chart. -/
@[reassoc] theorem retainedTrivializedPositiveChart_final_cyclic :
    pos ≫ t = Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a).toRingHom) ≫
      torus ≫ ProjectiveLine.endpointReversal F ≫ C 0 := by
  rw [finalAdjacentComponent,
    retainedTrivializedPositiveChart_adjacent_cyclic A hπ data D j.val
      (by omega) (by omega) (by omega) (by omega) m (by omega) r]
  simp only [Category.assoc]

/-- Final-stage transport also retains the negative chart's signed inverse scaling. -/
@[reassoc] theorem retainedTrivializedNegativeChart_final_cyclic :
    neg ≫ t = Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
      torus ≫ C 1 := by
  rw [finalAdjacentComponent,
    retainedTrivializedNegativeChart_adjacent_cyclic A hπ data D j.val
      (by omega) (by omega) (by omega) (by omega) m (by omega) r]
  simp only [Category.assoc]

variable (hstart : start = 0)

/-- Positive retained positions in the actual complete odd cycle keep their arithmetic scale. -/
@[reassoc] theorem retainedTrivializedPositiveChart_odd_cyclic
    (hp : 2 * (start + s + 1) < depth) :
    pos ≫ t = Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a).toRingHom) ≫
      torus ≫ (zeroSplitCycleComponent hπ data D s hs hstart hk hp
        ⟨j.val + 1, by omega⟩).left := by
  rw [zeroSplitCycleComponent_first hπ data D s hs hstart hk hp ⟨j.val, by omega⟩,
    finalBranchComponent_adjacent hπ data D s hs hk hp j 0]
  exact retainedTrivializedPositiveChart_final_cyclic A hπ data D r s hs hk j

/-- Negative retained positions in the complete odd cycle keep their signed inverse scale. -/
@[reassoc] theorem retainedTrivializedNegativeChart_odd_cyclic
    (hp : 2 * (start + s + 1) < depth) :
    neg ≫ t = Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
      torus ≫ (zeroSplitCycleComponent hπ data D s hs hstart hk hp
        ⟨2 * s + 2 - j.val, by omega⟩).left := by
  rw [zeroSplitCycleComponent_second hπ data D s hs hstart hk hp ⟨j.val, by omega⟩,
    finalBranchComponent_adjacent hπ data D s hs hk hp j 1]
  exact retainedTrivializedNegativeChart_final_cyclic A hπ data D r s hs hk j

/-- Positive retained positions in the even cycle have the same actual arithmetic scale. -/
@[reassoc] theorem retainedTrivializedPositiveChart_even_cyclic
    (hp : 2 * (start + s + 1) = depth) :
    pos ≫ t = Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling a).toRingHom) ≫
      torus ≫ (zeroEqualityCycleComponent hπ data D s hs hstart hk hp
        ⟨j.val + 1, by omega⟩).left := by
  rw [zeroEqualityCycleComponent_first]
  exact retainedTrivializedPositiveChart_final_cyclic A hπ data D r s hs hk j

/-- Negative retained positions in the even cycle retain the original signed inverse scale. -/
@[reassoc] theorem retainedTrivializedNegativeChart_even_cyclic
    (hp : 2 * (start + s + 1) = depth) :
    neg ≫ t = Spec.map (CommRingCat.ofHom (PolygonScaledReciprocal.scaling (-a)⁻¹).toRingHom) ≫
      torus ≫ (zeroEqualityCycleComponent hπ data D s hs hstart hk hp
        ⟨2 * s + 1 - j.val, by omega⟩).left := by
  rw [zeroEqualityCycleComponent_second]
  exact retainedTrivializedNegativeChart_final_cyclic A hπ data D r s hs hk j

end FLT.Mazur.WeierstrassDividedDepth
