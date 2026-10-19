/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalIntegralKernelClosure
public import FLT.Mazur.WeierstrassGenericKernelRecovery

/-!
# Recovering the original prime kernel from its constructed integral closure

The closure has exactly the original transported generic kernel, with the same
closed inclusion and structure map. No abstract substitute kernel is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
  (hq : Function.Surjective q)
  {L R : Type} [Field L] [CommRing R] [Algebra ℚ L] [Algebra R L]
  [IsFractionRing R L] (W : WeierstrassCurve R) (C : VariableChange L)
  (hC : C • E.map (algebraMap ℚ L) = W.map (algebraMap R L))

local notation "i" => primeKernelRationalMap E p q hq hfixed
local notation "iL" => localGenericKernelInclusion E W C hC i

/-- The original prime inclusion is recovered from its integral schematic closure. -/
theorem primeLocalIntegralKernelClosure_inclusion_isPullback :
    IsPullback (genericKernelToClosure W iL) iL (genericKernelClosureInclusion W iL)
      (integralCoefficientMorphism W) := genericKernelClosureInclusion_isPullback W iL

/-- The actual closure's generic fiber is the full original prime kernel. -/
theorem primeLocalIntegralKernelClosure_structure_isPullback :
    IsPullback (genericKernelToClosure W iL)
      (iL ≫ integralCurveStructure (W.map (algebraMap R L)))
      (genericKernelClosureStructure W iL) (Spec.map (CommRingCat.ofHom (algebraMap R L))) :=
  genericKernelClosureStructure_isPullback W iL

/-- The constructed generic-fiber isomorphism retains the exact transported original kernel. -/
def primeLocalIntegralKernelClosureGenericIso : localGenericKernel E W C hC i ≅
    pullback (genericKernelClosureStructure W iL)
      (Spec.map (CommRingCat.ofHom (algebraMap R L))) := genericKernelClosureGenericIso W iL

end WeierstrassCurve.Velu
