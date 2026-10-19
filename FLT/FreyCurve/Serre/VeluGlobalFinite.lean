/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalPointKernel
public import FLT.FreyCurve.Serre.VeluGlobalProperSurjective
public import FLT.Mazur.CurveFinite
public import FLT.Mazur.SmoothCurveDimension
public import FLT.Mazur.WeierstrassIntegralSmooth

/-!
# Finiteness of the original global Vélu morphism

An original point outside the finite subgroup has nonzero image. This makes
the actual map nonconstant; properness and source dimension one imply finiteness.
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

/-- The actual scheme map is nonconstant, witnessed by original field-valued points. -/
theorem veluGlobalMorphism_nonconstant :
    ∃ a b : integralCurve E, veluGlobalMorphism E G hodd a ≠ veluGlobalMorphism E G hodd b := by
  let _ := infinite_points E
  obtain ⟨P, hP⟩ := (Set.toFinite (G : Set E.toAffine.Point)).exists_notMem
  let a := affineSmoothPoint E P ≫ (integralSmoothOpen E).ι
  let b := integralCurveZero E
  have hneq : a ≫ veluGlobalMorphism E G hodd ≠ b ≫ veluGlobalMorphism E G hodd := by
    rw [veluGlobalMorphism_zero]
    exact fun h => hP ((veluGlobalMorphism_point_kernel_iff E G hodd P).mp h)
  refine ⟨a (IsLocalRing.closedPoint K), b (IsLocalRing.closedPoint K), ?_⟩
  intro h
  apply hneq
  apply ext_of_apply_closedPoint_eq (integralCurveStructure (curve E G))
  · rw [Category.assoc, veluGlobalMorphism_base]
    exact affineSmoothPoint_section E P
  · rw [Category.assoc, veluGlobalMorphism_base]
    exact integralCurveZero_structure E
  · exact h

/-- The original global Vélu morphism is finite on the entire actual source cubic. -/
instance veluGlobalMorphism_isFinite : IsFinite (veluGlobalMorphism E G hodd) := by
  let _ := integralCurveStructure_smooth_dimension E IsElliptic.isUnit
  exact FLT.Mazur.FCurve.nonconstantProperCurveFinite (integralCurveStructure E)
    (integralCurveStructure (curve E G)) (veluGlobalMorphism E G hodd)
    inferInstance inferInstance
    (FLT.Mazur.FCurve.smoothCurveDimension (integralCurveStructure E)
      inferInstance inferInstance).le
    inferInstance (veluGlobalMorphism_base E G hodd) (veluGlobalMorphism_nonconstant E G hodd)

/-- Every original target scheme point has a finite fiber. -/
theorem veluGlobalMorphism_finite_fiber (y : integralCurve (curve E G)) :
    (veluGlobalMorphism E G hodd ⁻¹' {y}).Finite :=
  (veluGlobalMorphism E G hodd).finite_preimage_singleton y

end WeierstrassCurve.Velu
