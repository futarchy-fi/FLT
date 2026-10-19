/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericKernelClosure
public import FLT.Mazur.SchematicDenseBezoutFlat
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Flatness of the actual generic kernel closure over any valuation ring

Geometric local fields need not have discrete valuations. Torsion detected on
the dense generic source gives flatness over a Bezout domain, so the same actual
closure is flat over geometric valuation rings without a Noetherian hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve R) {H : Scheme}
  (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]

/-- The exact generic closure is flat over any Bezout domain, including valuation rings. -/
theorem genericKernelClosureStructure_flat_bezout
    [Flat (i ≫ integralCurveStructure (W.map (algebraMap R K)))] :
    Flat (genericKernelClosureStructure W i) := by
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  let _ : IsDomain Γ(Spec (.of R), ⊤) := e.toMulEquiv.isDomain _
  let _ : IsBezout Γ(Spec (.of R), ⊤) := e.symm.surjective.isBezout e.symm.toRingHom
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
  let _ : Flat (genericKernelToClosure W i ≫ genericKernelClosureStructure W i) := by
    rw [genericKernelToClosure_structure]
    infer_instance
  exact SchematicDenseBezoutFlat.flat (genericKernelToClosure W i)
    (genericKernelClosureStructure W i)

end FLT.Mazur.WeierstrassIntegralChart
