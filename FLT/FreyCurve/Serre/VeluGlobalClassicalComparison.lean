/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalPointValues
public import FLT.FreyCurve.Serre.VeluElliptic

/-!
# The global scheme map is the original classical Vélu point map

The already proved nonsingularity of the exact target closes the comparison
with the original pointMap, both on and off the original subgroup.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup E.toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The actual global morphism induces exactly the original classical pointMap. -/
@[reassoc] theorem veluGlobalMorphism_pointMap (P : E.toAffine.Point) :
    (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) ≫ veluGlobalMorphism E G hodd =
      affineSmoothPoint (curve E G)
        (pointMap E G (curve E G) (nonsingular_xMap_yMap_of_not_mem E G hodd) P) ≫
        (integralSmoothOpen (curve E G)).ι := by
  by_cases hP : P ∈ G
  · rw [veluGlobalMorphism_kernel E G hodd P hP,
      (pointMap_eq_zero_iff E G (curve E G) _ P).mpr hP]
    change _ = affineSmoothPoint (curve E G)
      (0 : ((curve E G).map (algebraMap K K)).toAffine.Point) ≫ _
    rw [affineSmoothPoint_zero]
    change _ = Spec.map (𝟙 (CommRingCat.of K)) ≫ integralCurveZero (curve E G)
    rw [Spec.map_id, Category.id_comp]
  · cases P with
    | zero => exact (hP G.zero_mem).elim
    | some u v hQ =>
      rw [veluGlobalMorphism_affineNonkernel E G hodd hQ hP]
      simp only [pointMap, dite_eq_right hP]
      rw [affineSmoothPoint_some]
      rfl

end WeierstrassCurve.Velu
