/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLocalGenericKernel
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The original local kernel's coefficient square

The source kernel over the changed local equation is the exact base change of
its original coefficient structure. Finiteness and étaleness follow from this
square without any choice of the rational quotient target.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassLocalKernelCoefficientSquare
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {K L R : Type} [CommRing K] [CommRing L] [CommRing R]
  [Algebra K L] [Algebra R L]
  (E : WeierstrassCurve K) (W : WeierstrassCurve R) (C : VariableChange L)
  (hC : C • E.map (algebraMap K L) = W.map (algebraMap R L))
  {H : Scheme} (i : H ⟶ integralCurve E)

/-- The original embedded kernel's coefficient square is Cartesian. -/
theorem isPullback :
    IsPullback (localGenericKernelOriginal E W C hC i)
      (localGenericKernelInclusion E W C hC i ≫
        integralCurveStructure (W.map (algebraMap R L)))
      (i ≫ integralCurveStructure E)
      (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  (localGenericKernel_isPullback E W C hC i).flip.paste_vert
    (localGenericProjection_isPullback E W C hC)

/-- Finiteness of the original coefficient structure survives the exact local transport. -/
theorem isFinite [IsFinite (i ≫ integralCurveStructure E)] :
    IsFinite (localGenericKernelInclusion E W C hC i ≫
      integralCurveStructure (W.map (algebraMap R L))) :=
  MorphismProperty.of_isPullback (isPullback E W C hC i) inferInstance

/-- Étaleness of the original coefficient structure survives the exact local transport. -/
theorem etale [Etale (i ≫ integralCurveStructure E)] :
    Etale (localGenericKernelInclusion E W C hC i ≫
      integralCurveStructure (W.map (algebraMap R L))) :=
  MorphismProperty.of_isPullback (isPullback E W C hC i) inferInstance

end FLT.Mazur.WeierstrassLocalKernelCoefficientSquare
