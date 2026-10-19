/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalGenericKernel
public import FLT.Mazur.WeierstrassGenericKernelClosure

/-!
# Constructing the original prime kernel's proper flat integral closure

The full original rational kernel, transported to the specified generic
source, determines a schematic closure in the original integral equation.
Its flatness follows from the proved generic degree p, including at p.
This does not yet prove finiteness or extend the quotient over singular fibers.
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
local instance integralKernelClosureFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (integralKernelClosureFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  (hq : Function.Surjective q)

variable {L R : Type} [Field L] [CommRing R] [Algebra ℚ L] [Algebra R L]
  (W U : WeierstrassCurve R) (C D : VariableChange L)
  (hC : C • E.map (algebraMap ℚ L) = W.map (algebraMap R L))
  (hD : D • V.map (algebraMap ℚ L) = U.map (algebraMap R L))


local notation "i" => primeKernelRationalMap E p q hq hfixed
local notation "iL" => localGenericKernelInclusion E W C hC i

include hp hcurve hD in
/-- The actual schematic closure of the original prime kernel is flat over the integral base. -/
theorem primeLocalGenericKernelClosure_flat [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Flat R L] : Flat (genericKernelClosureStructure W iL) := by
  let _ : Flat (iL ≫ integralCurveStructure (W.map (algebraMap R L))) :=
    (primeLocalGenericGroupHom_kernel_degree E p q hp V hcurve hfixed hq W U C D hC hD).2.1
  exact genericKernelClosureStructure_flat W iL

include hp hcurve hD in
/-- The retained kernel admits a constructed proper flat closed integral model and factorization. -/
theorem exists_primeLocalIntegralKernelClosure [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Flat R L] :
    ∃ (H : Scheme) (j : H ⟶ integralCurve W)
      (a : localGenericKernel E W C hC i ⟶ H),
      IsClosedImmersion j ∧ IsProper (j ≫ integralCurveStructure W) ∧
      Flat (j ≫ integralCurveStructure W) ∧
      IsSchemeTheoreticallyDominant a ∧
      a ≫ j = iL ≫ integralCoefficientMorphism W := by
  refine ⟨genericKernelClosure W iL, genericKernelClosureInclusion W iL,
    genericKernelToClosure W iL, inferInstance, inferInstance, ?_, inferInstance,
    genericKernelToClosure_inclusion W iL⟩
  exact primeLocalGenericKernelClosure_flat E p q hp V hcurve hfixed hq W U C D hC hD

end WeierstrassCurve.Velu
