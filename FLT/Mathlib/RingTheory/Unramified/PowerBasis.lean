/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.PowerBasisDifferentials
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Unramified.Basic

/-!
# Rigidity of maps from monogenic unramified algebras

The differential-annihilator formula makes the minimal-polynomial derivative
of a power-basis generator a unit. Maps into a local ring which agree in the
residue field must therefore agree everywhere.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace PowerBasis

variable {R C S : Type*} [CommRing R] [CommRing C] [Algebra R C]
  [Algebra.FormallyUnramified R C]

/-- The derivative of an integral power-basis generator is a unit in an
unramified algebra. -/
theorem isUnitDerivativeOfUnramified (pb : PowerBasis R C) :
    IsUnit (aeval pb.gen (minpoly R pb.gen).derivative) := by
  rw [← Ideal.span_singleton_eq_top, ← pb.annihilator_kaehlerDifferential]
  exact Module.annihilator_eq_top_iff.mpr inferInstance

/-- Two maps from a monogenic unramified algebra into a local ring are equal
if their generator images agree in the residue field. -/
theorem algHomEqOfResidueEq [CommRing S] [IsLocalRing S] [Algebra R S]
    (pb : PowerBasis R C) (f g : C →ₐ[R] S)
    (hres : residue S (f pb.gen) = residue S (g pb.gen)) : f = g := by
  apply pb.algHom_ext
  apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    (f := (minpoly R pb.gen).map (algebraMap R S))
  · rw [eval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  · rw [eval_map_algebraMap, aeval_algHom_apply, minpoly.aeval, map_zero]
  · change f pb.gen - g pb.gen ∈ maximalIdeal S
    rw [← residue_eq_zero_iff, map_sub, hres, sub_self]
  · rw [derivative_map, eval_map_algebraMap, aeval_algHom_apply]
    exact pb.isUnitDerivativeOfUnramified.map f

end PowerBasis
