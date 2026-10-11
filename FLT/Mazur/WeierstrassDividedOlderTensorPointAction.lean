/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderCubicAction
public import FLT.Mazur.WeierstrassDividedGlobalCoefficientAction

/-!
# Recovering coefficient actions from both original projections

Scalar extension of an algebra point has the prescribed coefficient map
and the original integral point as its two projections. These projections
upgrade an integral action equality to the actual coefficient-model action.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (j : ℕ) (hj : j + 1 ≤ n) (r : ℕ) (hr : j + 1 + r ≤ n)
  (S C : Type u) [CommRing S] [CommRing C] [Algebra R S] [Algebra S C]
  [Algebra R C] [IsScalarTower R S C]
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "A" => WeierstrassSuccessiveX.Coordinate W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "base" => finiteGlobalStructure hπ data (j + 1 + r) hr
local notation "fst" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S))) base
local notation "snd" => pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S))) base
local notation "c" => olderGlobalChart hπ data j hj r hr
local notation "cS" => olderGlobalTensorChart hπ data S j hj r hr

/-- The original algebra point extended to the actual retained coefficient chart. -/
def olderGlobalTensorAlgebraPoint (f : A →ₐ[R] C) :
    Spec (.of C) ⟶ finiteGlobalTensorModel hπ data S (j + 1 + r) hr :=
  Spec.map (CommRingCat.ofHom (AlgHom.liftEquiv R S A C f).toRingHom) ≫ cS

/-- The extended algebra point retains every original coefficient. -/
@[reassoc] theorem olderGlobalTensorAlgebraPoint_structure (f : A →ₐ[R] C) :
    olderGlobalTensorAlgebraPoint hπ data j hj r hr S C f ≫ fst =
      Spec.map (CommRingCat.ofHom (algebraMap S C)) := by
  rw [olderGlobalTensorAlgebraPoint, Category.assoc, olderGlobalTensorChart_structure]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext (AlgHom.liftEquiv R S A C f).commutes

/-- The other projection is the same original integral algebra point. -/
@[reassoc] theorem olderGlobalTensorAlgebraPoint_projection (f : A →ₐ[R] C) :
    olderGlobalTensorAlgebraPoint hπ data j hj r hr S C f ≫ snd =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫ c := by
  rw [olderGlobalTensorAlgebraPoint, Category.assoc, olderGlobalTensorChart_integralProjection]
  have he : Spec.map (CommRingCat.ofHom (AlgHom.liftEquiv R S A C f).toRingHom) ≫
      TensorOpenChart.projection = Spec.map (CommRingCat.ofHom f.toRingHom) := by
    rw [TensorOpenChart.projection, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro q
    exact AlgHom.liftEquiv_tmul f (1 : S) q |>.trans (one_smul S _)
  rw [← Category.assoc, he]

variable (a : Spec (.of C) ⟶ (integralSmoothOpen (W.map (algebraMap R S))).toScheme)
  (ha : a ≫ integralSmoothStructure (W.map (algebraMap R S)) =
    Spec.map (CommRingCat.ofHom (algebraMap S C)))

include ha in
/-- The original extended smooth parameter is compatible with every extended algebra point. -/
theorem olderGlobalTensorAlgebraPoint_condition (f : A →ₐ[R] C) :
    a ≫ integralSmoothStructure (W.map (algebraMap R S)) =
      olderGlobalTensorAlgebraPoint hπ data j hj r hr S C f ≫ fst := by
  rw [olderGlobalTensorAlgebraPoint_structure]
  exact ha

/-- Both projections transport a proved integral action to the actual coefficient action. -/
theorem olderGlobalTensorAlgebraPoint_action (f g : A →ₐ[R] C)
    (hadd : finiteGlobalPointAction hπ data (j + 1 + r) hr
      (a ≫ originalSmoothCoefficientMap S W)
      (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ c)
      (olderGlobalChart_algebra_condition hπ data j hj r hr
        (a ≫ originalSmoothCoefficientMap S W) f (by
          rw [Category.assoc, originalSmoothCoefficientMap_structure, ← Category.assoc, ha]
          exact specAlgHom_structure (IsScalarTower.toAlgHom R S C))) =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ c) :
    finiteGlobalCoefficientPointAction hπ data (j + 1 + r) hr S a
      (olderGlobalTensorAlgebraPoint hπ data j hj r hr S C f)
      (olderGlobalTensorAlgebraPoint_condition hπ data j hj r hr S C a ha f) =
        olderGlobalTensorAlgebraPoint hπ data j hj r hr S C g := by
  apply pullback.hom_ext
  · rw [finiteGlobalCoefficientPointAction_structure,
      olderGlobalTensorAlgebraPoint_structure, ha]
  · simpa only [finiteGlobalCoefficientPointAction_projection,
      olderGlobalTensorAlgebraPoint_projection] using hadd

end FLT.Mazur.WeierstrassDividedDepth
