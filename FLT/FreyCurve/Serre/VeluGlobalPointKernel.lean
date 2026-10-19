/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalPointValues
public import FLT.Mazur.WeierstrassAffinePointNonzero

/-!
# The original point kernel of the actual global Vélu morphism

Nonkernel points land in the target affine chart, which excludes infinity.
Thus the actual global morphism has exactly the original subgroup as its
kernel on base-field points. Scheme-theoretic fiber equality is separate.
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

/-- Original nonkernel affine points cannot map to the target identity. -/
theorem veluGlobalMorphism_affineNonkernel_ne_zero {u v : K}
    (hP : E.toAffine.Nonsingular u v) (hPG : Affine.Point.some u v hP ∉ G) :
    (affineSmoothPoint E (.some u v hP) ≫ (integralSmoothOpen E).ι) ≫
      veluGlobalMorphism E G hodd ≠ integralCurveZero (curve E G) := by
  rw [veluGlobalMorphism_affineNonkernel E G hodd hP hPG]
  have h := affine_evaluation_ne_zero (curve E G) (veluTargetPointChart E G hodd hP hPG)
  change _ ≠ Spec.map (𝟙 (CommRingCat.of K)) ≫ integralCurveZero (curve E G) at h
  simpa only [Spec.map_id, Category.id_comp] using h

/-- The kernel on original field-valued points is precisely the original finite subgroup. -/
theorem veluGlobalMorphism_point_kernel_iff (P : E.toAffine.Point) :
    (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) ≫ veluGlobalMorphism E G hodd =
      integralCurveZero (curve E G) ↔ P ∈ G := by
  constructor
  · intro h
    cases P with
    | zero => exact G.zero_mem
    | some u v hP =>
      by_contra hPG
      exact veluGlobalMorphism_affineNonkernel_ne_zero E G hodd hP hPG h
  · exact veluGlobalMorphism_kernel E G hodd P

/-- Every actual section killed by the global map comes from the original subgroup. -/
theorem veluGlobalMorphism_section_kernel (p : Spec (.of K) ⟶ integralCurve E)
    (hp : p ≫ integralCurveStructure E = 𝟙 _)
    (hz : p ≫ veluGlobalMorphism E G hodd = integralCurveZero (curve E G)) :
    ∃ P : G, affineSmoothPoint E P.val ≫ (integralSmoothOpen E).ι = p := by
  obtain ⟨P, hP⟩ := exists_affineSmoothPoint_of_section E p hp
  refine ⟨⟨P, (veluGlobalMorphism_point_kernel_iff E G hodd P).mp ?_⟩, hP⟩
  rwa [hP]

end WeierstrassCurve.Velu
