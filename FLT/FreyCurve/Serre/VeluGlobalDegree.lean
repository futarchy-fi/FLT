/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluElliptic
public import FLT.FreyCurve.Serre.VeluGlobalKernelCardinality
public import FLT.Mazur.DominantSmoothCurveFlat
public import FLT.Mazur.FCurveContracts

/-!
# The actual global Vélu map has degree equal to its original subgroup order

Flatness follows on the actual valuation stalks of the smooth target.
The exact kernel computes rank at infinity; connectedness makes it constant.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The original global morphism is flat over the exact original target cubic. -/
instance veluGlobalMorphism_flat : Flat (veluGlobalMorphism E G hodd) := by
  let _ := integralCurveStructure_smooth_dimension (curve E G)
    (curve_isElliptic E G hodd).isUnit
  exact FLT.Mazur.FCurve.dominantIntegral_smoothCurve_flat
    (veluGlobalMorphism E G hodd) (integralCurveStructure (curve E G))

/-- The finite global morphism is locally finitely presented over its original target. -/
instance veluGlobalMorphism_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (veluGlobalMorphism E G hodd) := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian (integralCurveStructure (curve E G))
  infer_instance

/-- The rank of the original global morphism is the order of the original finite subgroup. -/
theorem veluGlobalMorphism_rank (y : integralCurve (curve E G)) :
    (veluGlobalMorphism E G hodd).finrank y = Nat.card G := by
  let z := integralCurveZero (curve E G) (IsLocalRing.closedPoint K)
  have hc := congrFun ((veluGlobalMorphism E G hodd).isLocallyConstant_finrank.eq_const y) z
  have hz : (veluGlobalMorphism E G hodd).finrank z = Nat.card G := by
    rw [← Scheme.Hom.finrank_pullback_snd (veluGlobalMorphism E G hodd)
      (integralCurveZero (curve E G)) (IsLocalRing.closedPoint K)]
    exact veluGlobalKernel_rank E G hodd _
  exact hc.symm.trans hz

/-- The actual map is finite locally free of exactly the original subgroup order. -/
theorem veluGlobalMorphism_degree :
    FLT.Mazur.FCurve.FiniteLocallyFreeDegree (veluGlobalMorphism E G hodd) (Nat.card G) :=
  ⟨inferInstance, inferInstance, inferInstance, veluGlobalMorphism_rank E G hodd⟩

end WeierstrassCurve.Velu
