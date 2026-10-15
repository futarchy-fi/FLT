/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGlobalTensorIntersection
public import FLT.Mazur.WeierstrassDividedArithmeticNodeCoverage

/-!
# The full terminal intersection in the original arithmetic stage

The actual divided and newest successive tensor charts meet along the entire
original depth boundary. The coordinate comparison retains the existing
successive arithmetic chart, so the constructed node opens use this same atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- The whole original divided tensor chart in the actual arithmetic stage. -/
def finiteArithmeticDividedTensorChart (j : ℕ) (hj : j ≤ n) :
    Spec (.of (WeierstrassDilatation.ScalarExtension W (π ^ (start + j))
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
      (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 Q)) ⟶
        finiteGlobalArithmeticStage hπ data j hj m :=
  globalDividedTensorChart hπ data Q j hj ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data j hj)).hom

/-- The original divided arithmetic chart is an open immersion. -/
theorem finiteArithmeticDividedTensorChart_isOpenImmersion (j : ℕ) (hj : j ≤ n) :
    IsOpenImmersion (finiteArithmeticDividedTensorChart hπ data m j hj) := by
  unfold finiteArithmeticDividedTensorChart
  infer_instance

/-- The divided arithmetic chart uses the original quotient coefficient map. -/
@[reassoc] theorem finiteArithmeticDividedTensorChart_structure (j : ℕ) (hj : j ≤ n) :
    finiteArithmeticDividedTensorChart hπ data m j hj ≫
      finiteGlobalArithmeticStructure hπ data j hj m =
        Spec.map (CommRingCat.ofHom (algebraMap Q
          (WeierstrassDilatation.ScalarExtension W (π ^ (start + j))
            (data ⟨j, Nat.lt_succ_of_le hj⟩).b3 (data ⟨j, Nat.lt_succ_of_le hj⟩).b4
            (data ⟨j, Nat.lt_succ_of_le hj⟩).b6 Q))) := by
  change (globalDividedTensorChart hπ data Q j hj ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data j hj)).hom) ≫
      pullback.snd (finiteGlobalStructure hπ data j hj) q = _
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, globalDividedTensorChart_structure]

variable (j : ℕ) (hj : j + 1 ≤ n)
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 d) (Data.b4 d) (Data.b6 d) 0
local notation "a" => depthOverlapEquiv W π (start + j) (Data.b3 d) (Data.b4 d) (Data.b6 d)

/-- The newest full successive tensor chart in the same arithmetic stage. -/
def finiteArithmeticNewestTensorChart :
    Spec (.of (ScalarExtension W (π ^ (start + j)) π
      (Data.b3 d) (Data.b4 d) (Data.b6 d) Q)) ⟶
        finiteGlobalArithmeticStage hπ data (j + 1) hj m :=
  globalSuccessiveTensorChart hπ data Q j hj ≫
    (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 1) hj)).hom

/-- The tensor source is the presentation used by the existing arithmetic node charts. -/
theorem finiteArithmeticNewestTensorChart_coordinates :
    Spec.map (CommRingCat.ofHom (baseChangeEquiv W (π ^ (start + j)) π
      (Data.b3 d) (Data.b4 d) (Data.b6 d) Q).toRingHom) ≫
        finiteArithmeticNewestTensorChart hπ data m j hj =
          finiteArithmeticSuccessiveChart hπ data j hj m := rfl

/-- The terminal arithmetic intersection is exactly the original depth principal boundary. -/
theorem terminalArithmeticTensor_isPullback :
    IsPullback ((PrincipalOpenTensor.transitionIso Q x t a).hom ≫
      PrincipalOpenTensor.inclusion Q x) (PrincipalOpenTensor.inclusion Q t)
      (finiteArithmeticDividedTensorChart hπ data m (j + 1) hj)
      (finiteArithmeticNewestTensorChart hπ data m j hj) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (pullbackSymmetry q (finiteGlobalStructure hπ data (j + 1) hj)).hom
    (globalTensor_depthOverlap_isPullback hπ data Q j hj).cone
    (globalTensor_depthOverlap_isPullback hπ data Q j hj).isLimit)

/-- The complete terminal principal boundary is the actual arithmetic fiber product. -/
def terminalArithmeticTensorPullbackIso :=
  (terminalArithmeticTensor_isPullback hπ data m j hj).isoPullback

/-- The arithmetic fiber product retains the original divided boundary projection. -/
@[reassoc] theorem terminalArithmeticTensorPullbackIso_divided :
    (terminalArithmeticTensorPullbackIso hπ data m j hj).hom ≫ pullback.fst _ _ =
      (PrincipalOpenTensor.transitionIso Q x t a).hom ≫ PrincipalOpenTensor.inclusion Q x :=
  (terminalArithmeticTensor_isPullback hπ data m j hj).isoPullback_hom_fst

/-- The arithmetic fiber product retains the original successive boundary projection. -/
@[reassoc] theorem terminalArithmeticTensorPullbackIso_successive :
    (terminalArithmeticTensorPullbackIso hπ data m j hj).hom ≫ pullback.snd _ _ =
      PrincipalOpenTensor.inclusion Q t :=
  (terminalArithmeticTensor_isPullback hπ data m j hj).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
