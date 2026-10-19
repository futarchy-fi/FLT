/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLocalGenericProjection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Transporting an original embedded kernel to specified local generic equations

Pull back the original inclusion along the actual local projection. Its original
scheme structure is retained, and the resulting inclusion is exactly the local
identity fiber whenever the two maps have the original coefficient square.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry WeierstrassCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L R : Type} [CommRing K] [CommRing L] [CommRing R]
  [Algebra K L] [Algebra R L]
  (E V : WeierstrassCurve K) (W U : WeierstrassCurve R) (C D : VariableChange L)
  (hC : C • E.map (algebraMap K L) = W.map (algebraMap R L))
  (hD : D • V.map (algebraMap K L) = U.map (algebraMap R L))

variable {H : Scheme} (i : H ⟶ integralCurve E)

/-- The exact original embedded scheme pulled back to the specified local source. -/
def localGenericKernel : Scheme := pullback (localGenericProjection E W C hC) i

/-- The original embedded scheme's inclusion in the specified local generic source. -/
def localGenericKernelInclusion :
    localGenericKernel E W C hC i ⟶ integralCurve (W.map (algebraMap R L)) :=
  pullback.fst _ _

/-- Projection to the original embedded scheme, retaining its full scheme structure. -/
def localGenericKernelOriginal : localGenericKernel E W C hC i ⟶ H := pullback.snd _ _

/-- The local kernel is defined by the actual Cartesian square of the original inclusion. -/
theorem localGenericKernel_isPullback :
    IsPullback (localGenericKernelInclusion E W C hC i)
      (localGenericKernelOriginal E W C hC i) (localGenericProjection E W C hC) i :=
  IsPullback.of_hasPullback _ _

/-- Closedness of the original inclusion is preserved on the specified local equation. -/
instance localGenericKernelInclusion_closed [IsClosedImmersion i] :
    IsClosedImmersion (localGenericKernelInclusion E W C hC i) :=
  MorphismProperty.of_isPullback (localGenericKernel_isPullback E W C hC i).flip
    (inferInstanceAs (IsClosedImmersion i))

variable (d : H ⟶ Spec (.of K)) (hi : i ≫ integralCurveStructure E = d)
  (f : integralCurve E ⟶ integralCurve V)
  (g : integralCurve (W.map (algebraMap R L)) ⟶ integralCurve (U.map (algebraMap R L)))
  (hg : g ≫ integralCurveStructure (U.map (algebraMap R L)) =
    integralCurveStructure (W.map (algebraMap R L)))
  (hsq : g ≫ localGenericProjection V U D hD = localGenericProjection E W C hC ≫ f)

include hi in
/-- The local structure map retains the original kernel's coefficient projection. -/
@[reassoc] theorem localGenericKernel_structure :
    localGenericKernelOriginal E W C hC i ≫ d =
      (localGenericKernelInclusion E W C hC i ≫
        integralCurveStructure (W.map (algebraMap R L))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [← hi, ← Category.assoc, ← (localGenericKernel_isPullback E W C hC i).w,
    Category.assoc, localGenericProjection_structure, Category.assoc]

include hi hg hsq in
/-- The original kernel remains killed by the actual local map. -/
@[reassoc] theorem localGenericKernel_zero (hz : i ≫ f = d ≫ integralCurveZero V) :
    localGenericKernelInclusion E W C hC i ≫ g =
      (localGenericKernelInclusion E W C hC i ≫
        integralCurveStructure (W.map (algebraMap R L))) ≫
          integralCurveZero (U.map (algebraMap R L)) := by
  apply localGenericProjection_hom_ext V U D hD
  · rw [Category.assoc, hsq, ← Category.assoc,
      (localGenericKernel_isPullback E W C hC i).w, Category.assoc, hz,
      ← Category.assoc, localGenericKernel_structure E W C hC i d hi]
    simp only [Category.assoc, localGenericProjection_zero]
  · rw [Category.assoc, hg, Category.assoc, integralCurveZero_structure, Category.comp_id]

include hi hg hsq in
/-- The exact original closed subscheme is the full local Cartesian identity fiber. -/
theorem localGenericKernel_identityFiber (hf : IsPullback i d f (integralCurveZero V)) :
    IsPullback (localGenericKernelInclusion E W C hC i)
      (localGenericKernelInclusion E W C hC i ≫
        integralCurveStructure (W.map (algebraMap R L))) g
      (integralCurveZero (U.map (algebraMap R L))) := by
  have B := (localGenericKernel_isPullback E W C hC i).paste_vert hf
  rw [localGenericKernel_structure E W C hC i d hi, ← hsq] at B
  exact B.of_bot (localGenericKernel_zero E V W U C D hC hD i d hi f g hg hsq hf.w)
    (localGenericProjection_zero_isPullback V U D hD)

end FLT.Mazur.WeierstrassIntegralChart
