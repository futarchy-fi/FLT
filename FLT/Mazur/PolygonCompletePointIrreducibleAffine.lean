/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleDivisorComplementAffine
public import FLT.Mazur.CurveDivisorAmpleSupport
public import FLT.Mazur.PolygonCompletePointCoordinateEquiv

/-!
# The original affine cubic comparison on irreducible field squares

The retained point meets the unique component, so its original divisor line
is ample and its actual complement is affine. The existing coordinate
morphism is then an isomorphism over the original specified field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve Scheme.Modules ModuleLineBundleTensorPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (L : Type) [Field L] {Y : Scheme}
  (s : Spec (.of L) ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s)

variable [IrreducibleSpace Y]

/-- On an irreducible original field square, every retained single-point line is ample. -/
theorem completeCartesianPointLine_ample_of_irreducible (i : Fin n) :
    AmpleLineBundle (completeCartesianPointLine K n h s p q hs i) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  let _ := completeCartesianPoint_isFinite K n h L s p q hs i
  apply (divisor_ample_iff_meets_components q
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1
    (completeCartesianField_classified K n h L s p q hs).pureDimension).mpr
  intro Z hZ
  have he : Z = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using hZ
  subst Z
  rw [Set.inter_univ, completeCartesianMarking_support]
  exact Set.range_nonempty _

/-- The actual retained point complement is affine on every irreducible field square. -/
theorem completeCartesianPointComplement_isAffine_of_irreducible (i : Fin n) :
    IsAffineOpen (completeCartesianPointComplement K n h L s p q hs i) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ : IsProper q := MorphismProperty.of_isPullback hs inferInstance
  exact isAffineOpen_divisorComplement q
    (completeCartesianMarking_relativeCartier K n h s p q hs i).1
    (completeCartesianPointLine_ample_of_irreducible K n h L s p q hs i)

/-- The existing original complement morphism is an isomorphism on irreducible squares. -/
theorem completeCartesianPointToAffineCubic_isIso_of_irreducible (i : Fin n) :
    IsIso (completeCartesianPointToAffineCubic K n h L s p q hs i) := by
  have ha := completeCartesianPointComplement_isAffine_of_irreducible K n h L s p q hs i
  let _ : IsAffine (completeCartesianPointComplement K n h L s p q hs i).toScheme := ha
  let _ : IsIso (CommRingCat.ofHom
      (completeCartesianPointCoordinateEvaluation K n h L s p q hs i)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (completeCartesianPointCoordinateRingEquiv K n h L s p q hs i).bijective
  unfold completeCartesianPointToAffineCubic
  infer_instance

/-- The actual retained point complement, identified by its existing coordinate morphism. -/
def completeCartesianPointAffineIso (i : Fin n) :
    (completeCartesianPointComplement K n h L s p q hs i).toScheme ≅
      Spec (.of
        (completeCartesianPointWeierstrass K n h L s p q hs i).toAffine.CoordinateRing) := by
  let _ := completeCartesianPointToAffineCubic_isIso_of_irreducible K n h L s p q hs i
  exact asIso (completeCartesianPointToAffineCubic K n h L s p q hs i)

/-- The affine isomorphism retains the original field square. -/
theorem completeCartesianPointAffineIso_over (i : Fin n) :
    (completeCartesianPointAffineIso K n h L s p q hs i).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap L
        (completeCartesianPointWeierstrass K n h L s p q hs i).toAffine.CoordinateRing)) =
      (completeCartesianPointComplement K n h L s p q hs i).ι ≫ q :=
  completeCartesianPointToAffineCubic_over K n h L s p q hs i

end FLT.Mazur.PolygonInfinitesimalStages
