/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupClosureGluing
public import FLT.Mazur.BinaryOpenDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Flatness and finite type of the glued subgroup closure

The two kernel quotients give a finite affine open cover. They are finitely
generated algebras, and over a DVR they are flat. These properties descend
to the glued scheme. Finiteness as a module is a separate global obligation.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

universe u

variable {K : Type u} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) (j k : Fin 3)

/-- The two actual affine chart closures form an open cover of their gluing. -/
def closureOpenCover : (gluedClosure A W H j k).OpenCover :=
  BinaryOpenDescent.cover (closureLeft A W H j k) (closureRight A W H j k)
    (closure_charts_cover A W H j k)

/-- Properties local on the source descend from the two closure charts. -/
theorem closureToBase_property (P : MorphismProperty Scheme) [IsZariskiLocalAtSource P]
    (hj : P (closureChartToBase A W H j)) (hk : P (closureChartToBase A W H k)) :
    P (closureToBase A W H j k) := by
  apply IsZariskiLocalAtSource.of_openCover (P := P) (closureOpenCover A W H j k)
  intro b
  cases b
  · change P (closureLeft A W H j k ≫ closureToBase A W H j k)
    rw [closureLeft_toBase]
    exact hj
  · change P (closureRight A W H j k ≫ closureToBase A W H j k)
    rw [closureRight_toBase]
    exact hk

/-- Each affine closure chart is a finitely generated valuation-ring algebra. -/
instance closure_finiteType : Algebra.FiniteType A (Closure A W H j) := by
  unfold Closure AffineGenericClosure.Coordinate WeierstrassIntegralChart.Coordinate
  infer_instance

/-- Each affine chart's structural morphism is locally of finite type. -/
instance closureChartToBase_locallyOfFiniteType :
    LocallyOfFiniteType (closureChartToBase A W H j) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The glued subgroup closure is locally of finite type over the valuation ring. -/
instance closureToBase_locallyOfFiniteType :
    LocallyOfFiniteType (closureToBase A W H j k) := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @LocallyOfFiniteType) (Q := RingHom.FiniteType)
  exact closureToBase_property A W H j k (@LocallyOfFiniteType) inferInstance inferInstance

/-- Over a DVR every affine chart of the subgroup closure is flat. -/
instance closureChartToBase_flat [IsDedekindDomain A] : Flat (closureChartToBase A W H j) := by
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr (closure_flat A W H j)

/-- Flatness descends to the glued subgroup closure over a DVR. -/
instance closureToBase_flat [IsDedekindDomain A] : Flat (closureToBase A W H j k) := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  exact closureToBase_property A W H j k (@Flat) inferInstance inferInstance

/-- The glued closure is quasi-compact, since the affine cover has two charts. -/
instance gluedClosure_compactSpace : CompactSpace (gluedClosure A W H j k) := by
  let U := closureOpenCover A W H j k
  let _ : Finite U.I₀ := inferInstanceAs (Finite Bool)
  have _ (b : U.I₀) : CompactSpace (U.X b) := by
    cases b <;> exact inferInstanceAs (CompactSpace (Spec _))
  exact U.compactSpace

/-- The structural morphism is quasi-compact as well as locally of finite type. -/
instance closureToBase_quasiCompact : QuasiCompact (closureToBase A W H j k) := by
  exact (@HasAffineProperty.iff_of_isAffine _ _
    instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat _ _
    (closureToBase A W H j k) inferInstance).mpr inferInstance

end FLT.Mazur.EllipticSubgroupChart
