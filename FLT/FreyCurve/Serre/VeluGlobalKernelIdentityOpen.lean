/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalFinite
public import FLT.FreyCurve.Serre.VeluInfinitySimpleFiber
public import FLT.Mazur.OpenFiberSection

/-!
# The identity is open in the original scheme-theoretic Vélu kernel

The kernel is the actual pullback of original infinity along the original
global map. Its identity section is open, by the explicit simple neighborhood.
No replacement of the kernel by its point set or reduction is made.
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

/-- The full original scheme-theoretic kernel of the actual global morphism. -/
abbrev veluGlobalKernel :=
  pullback (veluGlobalMorphism E G hodd) (integralCurveZero (curve E G))

/-- The actual scheme-theoretic kernel is finite over the original field. -/
instance veluGlobalKernel_finite :
    IsFinite (pullback.snd (veluGlobalMorphism E G hodd) (integralCurveZero (curve E G))) :=
  inferInstance

/-- The original source identity regarded as a section of the full kernel. -/
def veluGlobalKernelZero : Spec (.of K) ⟶ veluGlobalKernel E G hodd :=
  pullback.lift (integralCurveZero E) (𝟙 _) (by simp [veluGlobalMorphism_zero])

/-- The simple neighborhood retains the original global morphism. -/
@[reassoc] theorem veluGlobalMorphism_simple :
    veluSimpleOpenImmersion E G ≫ veluGlobalMorphism E G hodd =
      veluSimpleRegularMorphism E G hodd := by
  rw [veluSimpleOpenImmersion, Category.assoc, veluGlobalMorphism_infinity,
    veluSimpleRegularMorphism_restriction]

omit hodd [IsAlgClosed K] [E.IsElliptic] in
/-- The lifted local identity still equals the original source identity. -/
@[reassoc] theorem veluSimplePointLift_zero :
    veluSimplePointLift E G ≫ veluSimpleOpenImmersion E G = integralCurveZero E := by
  rw [veluSimpleOpenImmersion, veluSimplePointLift_restriction_assoc,
    veluInfinityPointLift_zero]

/-- The original identity section is an actual open immersion into the full kernel. -/
instance veluGlobalKernelZero_isOpenImmersion :
    IsOpenImmersion (veluGlobalKernelZero E G hodd) := by
  apply FLT.Mazur.OpenFiberSection.isOpenImmersion (veluSimpleOpenImmersion E G)
    (veluGlobalMorphism E G hodd) (integralCurveZero (curve E G))
    (veluSimplePointLift E G) (veluGlobalKernelZero E G hodd)
  · rw [veluSimplePointLift_zero, veluGlobalKernelZero, pullback.lift_fst]
  · exact pullback.lift_snd _ _ _
  · rw [veluGlobalMorphism_simple]
    exact veluSimpleRegularMorphism_identityFiber E G hodd

end WeierstrassCurve.Velu
