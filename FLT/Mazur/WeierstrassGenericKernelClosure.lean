/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralBaseChange
public import FLT.Mazur.WeierstrassIntegralProper
public import FLT.Mazur.ChowSourceClosure
public import FLT.Mazur.SchematicDenseDedekindFlat

/-!
# The schematic integral closure of an actual generic embedded kernel

Take the scheme-theoretic image of the original inclusion followed by the
actual coefficient projection. This constructs a proper integral closed
subscheme. A flat generic source forces its closure to be flat over a DVR.
No extension of the quotient map across a singular cubic is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  (W : WeierstrassCurve R) {H : Scheme}
  (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]

/-- The original generic inclusion, viewed in the exact integral cubic. -/
def genericKernelToIntegral : H ⟶ integralCurve W := i ≫ integralCoefficientMorphism W

/-- The original generic inclusion is quasi-compact in the integral cubic. -/
instance genericKernelToIntegral_quasiCompact : QuasiCompact (genericKernelToIntegral W i) := by
  let _ : QuasiCompact (integralCoefficientMorphism (S := K) W) :=
    MorphismProperty.of_isPullback (integralCoefficient_isPullback W).flip
      (inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
  exact inferInstanceAs (QuasiCompact (i ≫ integralCoefficientMorphism W))

/-- The constructed schematic closure of the original generic embedded kernel. -/
def genericKernelClosure : Scheme := (genericKernelToIntegral W i).image

/-- Its actual closed inclusion in the original integral equation. -/
def genericKernelClosureInclusion : genericKernelClosure W i ⟶ integralCurve W :=
  (genericKernelToIntegral W i).imageι

/-- The original generic scheme factors through its constructed integral closure. -/
def genericKernelToClosure : H ⟶ genericKernelClosure W i :=
  (genericKernelToIntegral W i).toImage

omit [IsClosedImmersion i] in
/-- The closure factorization retains exactly the original generic inclusion. -/
@[reassoc] theorem genericKernelToClosure_inclusion :
    genericKernelToClosure W i ≫ genericKernelClosureInclusion W i =
      i ≫ integralCoefficientMorphism W := (genericKernelToIntegral W i).toImage_imageι

/-- The constructed closure is a closed subscheme of the exact integral cubic. -/
instance genericKernelClosureInclusion_closed :
    IsClosedImmersion (genericKernelClosureInclusion W i) :=
  inferInstanceAs (IsClosedImmersion (genericKernelToIntegral W i).imageι)

/-- The closure's structural map to the original coefficient ring. -/
def genericKernelClosureStructure : genericKernelClosure W i ⟶ Spec (.of R) :=
  genericKernelClosureInclusion W i ≫ integralCurveStructure W

/-- Properness follows from the original projective cubic and the constructed closed immersion. -/
instance genericKernelClosureStructure_proper : IsProper (genericKernelClosureStructure W i) :=
  inferInstanceAs (IsProper (genericKernelClosureInclusion W i ≫ integralCurveStructure W))

/-- The original generic scheme is quasi-compact in its actual schematic closure. -/
instance genericKernelToClosure_quasiCompact : QuasiCompact (genericKernelToClosure W i) :=
  inferInstanceAs (QuasiCompact (genericKernelToIntegral W i).toImage)

/-- The full original generic scheme is schematically dense in the constructed closure. -/
instance genericKernelToClosure_schemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (genericKernelToClosure W i) :=
  Chow.toImage_schemeTheoreticallyDominant (genericKernelToIntegral W i)

omit [IsClosedImmersion i] in
/-- The closure retains the generic structure map over the original base. -/
@[reassoc] theorem genericKernelToClosure_structure :
    genericKernelToClosure W i ≫ genericKernelClosureStructure W i =
      (i ≫ integralCurveStructure (W.map (algebraMap R K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  rw [genericKernelClosureStructure, genericKernelToClosure_inclusion_assoc,
    Category.assoc, integralCoefficientMorphism_structure]

/-- A flat generic kernel has a flat schematic closure over the original principal domain. -/
theorem genericKernelClosureStructure_flat [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Flat R K] [Flat (i ≫ integralCurveStructure (W.map (algebraMap R K)))] :
    Flat (genericKernelClosureStructure W i) := by
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  let _ : IsDomain Γ(Spec (.of R), ⊤) := e.toMulEquiv.isDomain _
  let _ : IsPrincipalIdealRing Γ(Spec (.of R), ⊤) :=
    IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let _ : Flat (genericKernelToClosure W i ≫ genericKernelClosureStructure W i) := by
    rw [genericKernelToClosure_structure]
    infer_instance
  exact SchematicDenseDedekindFlat.flat (genericKernelToClosure W i)
    (genericKernelClosureStructure W i)

end FLT.Mazur.WeierstrassIntegralChart
