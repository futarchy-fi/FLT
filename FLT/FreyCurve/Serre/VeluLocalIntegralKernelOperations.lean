/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalGenericKernel
public import FLT.Mazur.WeierstrassGenericClosureZero
public import FLT.Mazur.WeierstrassIdentityFiberOperations

/-!
# Zero and inverse on the retained prime integral kernel

Construct the generic operations from the actual quotient's Cartesian identity
fiber, then extend them to its original schematic closure. No smoothness of the
whole integral cubic, or of the entire kernel closure, is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  [Fintype (torsionKernel E p q)] (hp : Odd p)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q

/-- Retain the same enumeration of the original geometric kernel. -/
local instance integralKernelOperationsFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (integralKernelOperationsFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  (hq : Function.Surjective q)

variable {L R : Type} [Field L] [CommRing R] [Algebra ℚ L] [Algebra R L]
  (W U : WeierstrassCurve R) (C D : VariableChange L)
  (hC : C • E.map (algebraMap ℚ L) = W.map (algebraMap R L))
  (hD : D • V.map (algebraMap ℚ L) = U.map (algebraMap R L))


local notation "i" => primeKernelRationalMap E p q hq hfixed
local notation "iL" => localGenericKernelInclusion E W C hC i

local notation "G" => primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD
local notation "PB" =>
  primeLocalGenericGroupHom_kernel E p q hp V hcurve hfixed hq W U C D hC hD
local notation "N" => FLT.Mazur.WeierstrassIdentityFiber.negation _ _ _ _ G iL _ PB
local notation "Z" => FLT.Mazur.WeierstrassIdentityFiber.zero _ _ _ _ G iL _ PB

/-- The actual prime closure's inverse, constructed from the original quotient. -/
def primeIntegralClosureNegation : genericKernelClosure W iL ⟶ genericKernelClosure W iL :=
  genericClosureNegation W iL N
    (FLT.Mazur.WeierstrassIdentityFiber.negation_inclusion _ _ _ _ G iL _ PB)

/-- The integral inverse retains the original ambient cubic inverse. -/
@[reassoc] theorem primeIntegralClosureNegation_inclusion :
    primeIntegralClosureNegation E p q hp V hcurve hfixed hq W U C D hC hD ≫
      genericKernelClosureInclusion W iL =
        genericKernelClosureInclusion W iL ≫ integralCurveNegation W :=
  genericClosureNegation_inclusion _ _ _ _

/-- The retained prime closure's inverse is involutive, including on singular fibers. -/
@[reassoc] theorem primeIntegralClosureNegation_comp :
    primeIntegralClosureNegation E p q hp V hcurve hfixed hq W U C D hC hD ≫
      primeIntegralClosureNegation E p q hp V hcurve hfixed hq W U C D hC hD = 𝟙 _ :=
  genericClosureNegation_comp _ _ _ _

variable [IsFractionRing R L]

/-- The actual prime closure's identity, extended from the original generic identity fiber. -/
def primeIntegralClosureZero : Spec (.of R) ⟶ genericKernelClosure W iL :=
  genericClosureZero W iL Z
    (FLT.Mazur.WeierstrassIdentityFiber.zero_inclusion _ _ _ _ G iL _ PB)

/-- The retained prime closure's identity is exactly the original cubic zero section. -/
@[reassoc] theorem primeIntegralClosureZero_inclusion :
    primeIntegralClosureZero E p q hp V hcurve hfixed hq W U C D hC hD ≫
      genericKernelClosureInclusion W iL = integralCurveZero W :=
  genericClosureZero_inclusion _ _ _ _

/-- The retained prime closure's identity is a section of its original integral structure. -/
@[reassoc] theorem primeIntegralClosureZero_structure :
    primeIntegralClosureZero E p q hp V hcurve hfixed hq W U C D hC hD ≫
      genericKernelClosureStructure W iL = 𝟙 _ := genericClosureZero_structure _ _ _ _

end WeierstrassCurve.Velu
