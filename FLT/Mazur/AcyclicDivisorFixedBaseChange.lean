/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeAcyclicDivisorCartesianMap
public import FLT.Mazur.RelativePicardBaseChangeGeometry

/-!
# Acyclic full divisors under change of the fixed coefficient base

Flattening the actual test-curve fiber product transports full acyclic
divisors in both directions. These constructions use the original and new
proper coefficient models separately, and retain the entire ideal.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open FCurve SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] (T : Over (Spec (.of R')))
local notation "q" => Limits.pullback.snd f a
local notation "U" => Functor.obj (Over.map a) T

omit [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  [IsProper f] [Flat f] [GeometricallyIntegral f] in
/-- The comparison of test curves is cartesian over the identity of the test. -/
theorem fixedBaseTotal_isPullback :
    IsPullback (relativeBaseChangeTotalIso f a T).hom
      (Limits.pullback.snd q T.hom) (Limits.pullback.snd f (U).hom) (𝟙 T.left) := by
  apply IsPullback.of_horiz_isIso
  exact ⟨by simp⟩

omit [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  [IsProper f] [Flat f] [GeometricallyIntegral f] in
/-- The inverse test-curve comparison is also cartesian over the original test. -/
theorem fixedBaseTotal_inv_isPullback :
    IsPullback (relativeBaseChangeTotalIso f a T).inv
      (Limits.pullback.snd f (U).hom) (Limits.pullback.snd q T.hom) (𝟙 T.left) := by
  let _ : IsIso (𝟙 T.left : (U).left ⟶ T.left) :=
    ⟨⟨𝟙 _, by simp, by simp⟩⟩
  apply IsPullback.of_horiz_isIso
  exact ⟨by simp⟩

/-- Transport full original acyclic divisors to the actual new coefficient model. -/
def acyclicDivisorFixedBaseChange
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f (U).hom)) :
    AcyclicRankOneRelativeDivisor (Limits.pullback.snd q T.hom) :=
  finiteTypeAcyclicDivisorCartesianMap (IsPullback.of_hasPullback f (U).hom)
    (IsPullback.of_hasPullback q T.hom) (fixedBaseTotal_isPullback f a T) D

/-- Recover full original divisors from the changed proper coefficient model. -/
def acyclicDivisorFixedBaseChangeInv
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd q T.hom)) :
    AcyclicRankOneRelativeDivisor (Limits.pullback.snd f (U).hom) :=
  finiteTypeAcyclicDivisorCartesianMap (IsPullback.of_hasPullback q T.hom)
    (IsPullback.of_hasPullback f (U).hom) (fixedBaseTotal_inv_isPullback f a T) D

/-- Forward transport pulls back the original full ideal along flattening. -/
theorem acyclicDivisorFixedBaseChange_ideal
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f (U).hom)) :
    (acyclicDivisorFixedBaseChange f a T D).val.val =
      D.val.val.comap (relativeBaseChangeTotalIso f a T).hom :=
  finiteTypeAcyclicDivisorCartesianMap_ideal _ _ _ D

/-- Reverse transport pulls the full ideal along the inverse flattening map. -/
theorem acyclicDivisorFixedBaseChangeInv_ideal
    (D : AcyclicRankOneRelativeDivisor (Limits.pullback.snd q T.hom)) :
    (acyclicDivisorFixedBaseChangeInv f a T D).val.val =
      D.val.val.comap (relativeBaseChangeTotalIso f a T).inv :=
  finiteTypeAcyclicDivisorCartesianMap_ideal _ _ _ D

/-- Fixed-base change gives a genuine equivalence on the full acyclic divisors. -/
def acyclicDivisorFixedBaseEquiv :
    AcyclicRankOneRelativeDivisor (Limits.pullback.snd f (U).hom) ≃
      AcyclicRankOneRelativeDivisor (Limits.pullback.snd q T.hom) where
  toFun := acyclicDivisorFixedBaseChange f a T
  invFun := acyclicDivisorFixedBaseChangeInv f a T
  left_inv D := by
    apply acyclicRankOneRelativeDivisor_ext
    rw [acyclicDivisorFixedBaseChangeInv_ideal, acyclicDivisorFixedBaseChange_ideal,
      ← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  right_inv D := by
    apply acyclicRankOneRelativeDivisor_ext
    rw [acyclicDivisorFixedBaseChange_ideal, acyclicDivisorFixedBaseChangeInv_ideal,
      ← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]

end FLT.Mazur.CartierAbel
