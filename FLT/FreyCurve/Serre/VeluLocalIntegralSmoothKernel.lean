/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalGenericKernel
public import FLT.Mazur.WeierstrassValuationClosureSmoothFlat
public import FLT.Mazur.WeierstrassGenericClosureSmoothOperations
public import FLT.Mazur.WeierstrassIdentityFiberOperations

/-!
# The actual prime kernel on the original smooth integral model

The same integral closure's smooth intersection has the full original generic
kernel, is flat and locally quasi-finite, and carries its original zero and inverse.
Its finiteness and integral degree p are not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
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
local instance integralSmoothKernelFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (integralSmoothKernelFintype E p q))
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


/-- The actual prime closure's inverse restricted to its original smooth intersection. -/
def primeIntegralSmoothKernelNegation :
    genericClosureSmoothPart W iL ⟶ genericClosureSmoothPart W iL :=
  genericClosureSmoothNegation W iL N
    (FLT.Mazur.WeierstrassIdentityFiber.negation_inclusion _ _ _ _ G iL _ PB)

/-- The smooth prime inverse retains the actual ambient smooth inverse. -/
@[reassoc] theorem primeIntegralSmoothKernelNegation_inclusion :
    primeIntegralSmoothKernelNegation E p q hp V hcurve hfixed hq W U C D hC hD ≫
      genericClosureSmoothInclusion W iL =
        genericClosureSmoothInclusion W iL ≫ integralSmoothNegation W :=
  genericClosureSmoothNegation_inclusion _ _ _ _

variable [IsFractionRing R L]

omit [Fintype (torsionKernel E p q)] in
/-- The original prime kernel is exactly the generic fiber of the smooth intersection. -/
theorem primeIntegralSmoothKernel_isPullback :
    IsPullback (genericKernelToClosureSmooth W (primeLocalSource_isElliptic E W C hC).isUnit iL)
      (iL ≫ integralCurveStructure (W.map (algebraMap R L)))
      (genericClosureSmoothStructure W iL) (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
  genericClosureSmoothStructure_isPullback W (primeLocalSource_isElliptic E W C hC).isUnit iL

/-- The actual prime closure's zero lies in its original smooth intersection. -/
def primeIntegralSmoothKernelZero : Spec (.of R) ⟶ genericClosureSmoothPart W iL :=
  genericClosureSmoothZero W iL Z
    (FLT.Mazur.WeierstrassIdentityFiber.zero_inclusion _ _ _ _ G iL _ PB)

/-- The smooth prime identity retains the actual ambient smooth identity. -/
@[reassoc] theorem primeIntegralSmoothKernelZero_inclusion :
    primeIntegralSmoothKernelZero E p q hp V hcurve hfixed hq W U C D hC hD ≫
      genericClosureSmoothInclusion W iL = integralSmoothZero W :=
  genericClosureSmoothZero_inclusion _ _ _ _

include hp hcurve hD in
/-- The retained prime smooth intersection is flat and locally quasi-finite at the original base. -/
theorem primeIntegralSmoothKernel_flat_locallyQuasiFinite [IsDomain R] [ValuationRing R] :
    Flat (genericClosureSmoothStructure W iL) ∧
      LocallyQuasiFinite (genericClosureSmoothStructure W iL) := by
  have hd := primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD
  let _ := hd.1
  let _ := hd.2.1
  exact ⟨genericClosureSmoothStructure_flat_valuation W iL,
    genericClosureSmoothStructure_locallyQuasiFinite W iL⟩

end WeierstrassCurve.Velu
