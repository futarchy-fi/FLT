/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAdicSharedCurveTower
public import FLT.Mazur.GeneralizedCurveBaseChangeTowerProjection
public import FLT.Mazur.CharacterSchemeIntrinsicMapComparison

/-!
# Intrinsic embeddings under extension of the shared finite ring

The actual shared curve tower preserves the original curve projection.
Consequently its intrinsic character embedding agrees with iterated pullback.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OneGonAdicIndependentModel
open Approximation OneGonAdicCharacterTower OneGonSmoothing CharacterSchemeBaseChange
open ArithmeticOneGonGeneralizedCurve WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

variable (I : Ideal R) [IsAdicComplete I R] (t : R) (ht : t ∈ I)
  (n : ℕ) [NeZero n] (s : Set R)
  (K L : Subalgebra ℤ R) [Algebra.FiniteType ℤ K] [Algebra.FiniteType ℤ L]
  (hS : base I t ht n s ≤ K) (hKL : K ≤ L) (hs : complementaryInverse I t ht ∈ s)

/-- The actual shared curve tower preserves the original curve projection. -/
@[reassoc] theorem sharedCurveTowerIso_fst_fst :
    (sharedCurveTowerIso I t ht n s K L hS hKL hs).hom.curve.left ≫
      Limits.pullback.fst
        (Limits.pullback.snd (curve I t ht n s hs).curve.hom
          (stageBaseMap I t ht n s (sharedStage I t ht n s K hS)))
        (sharedRingMap K L hKL) ≫
      Limits.pullback.fst (curve I t ht n s hs).curve.hom
        (stageBaseMap I t ht n s (sharedStage I t ht n s K hS)) =
      Limits.pullback.fst (curve I t ht n s hs).curve.hom
        (stageBaseMap I t ht n s (sharedStage I t ht n s L (hS.trans hKL))) := by
  let _ := sharedAlgebra I t ht n s K hS
  let _ := sharedAlgebra I t ht n s L (hS.trans hKL)
  let _ := sharedRingAlgebra K L hKL
  let _ : IsScalarTower (base I t ht n s) K L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  rw [sharedCurveTowerIso_def]
  exact GeneralizedEllipticCurve.baseChangeCompEqIso_curve_fst_fst
    (curve I t ht n s hs) (baseMap (base I t ht n s) K)
    (baseMap K L) (baseMap (base I t ht n s) L)
    (characterTower_baseMap (base I t ht n s) K L)

/-- The actual intrinsic embeddings commute with extension of the shared ring. -/
theorem shared_intrinsic_embedding_tower :
    ((stageCharacterIso I t ht n s (sharedStage I t ht n s L (hS.trans hKL))).hom ≫
      stageEmbedding I t ht n s (sharedStage I t ht n s L (hS.trans hKL)) hs) ≫
        (sharedCurveTowerIso I t ht n s K L hS hKL hs).hom.curve =
    (@overIso K L (ZMod n) _ _ (sharedRingAlgebra K L hKL) _).hom ≫
      (Over.pullback (sharedRingMap K L hKL)).map
        ((stageCharacterIso I t ht n s (sharedStage I t ht n s K hS)).hom ≫
          stageEmbedding I t ht n s (sharedStage I t ht n s K hS) hs) := by
  let _ := sharedAlgebra I t ht n s K hS
  let _ := sharedAlgebra I t ht n s L (hS.trans hKL)
  let _ := sharedRingAlgebra K L hKL
  let _ : IsScalarTower (base I t ht n s) K L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact intrinsicMap_comparison (base I t ht n s) K L (ZMod n)
    (curve I t ht n s hs).curve
    (Over.homMk (embedding I t ht n s) (embedding_structure I t ht n s))
    (sharedCurveTowerIso I t ht n s K L hS hKL hs).hom.curve
    (sharedCurveTowerIso_fst_fst I t ht n s K L hS hKL hs)

end FLT.Mazur.OneGonAdicIndependentModel
