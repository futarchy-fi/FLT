/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Algebraic pushouts from cartesian affine spectra

Reflection by the fully faithful spectrum functor recovers the actual
coefficient pushout from a cartesian square of affine schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SpecCartesianAlgebraPushout

universe u

/-- A cartesian square of spectra gives the pushout of its original ring maps. -/
theorem of_isPullback (R S A C : Type u) [CommRing R] [CommRing S]
    [CommRing A] [CommRing C] [Algebra R S] [Algebra R A] [Algebra R C]
    [Algebra S C] [Algebra A C] [IsScalarTower R S C] [IsScalarTower R A C]
    (h : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))
      (Spec.map (CommRingCat.ofHom (algebraMap S C)))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    Algebra.IsPushout R S A C := by
  apply CommRingCat.isPushout_iff_isPushout.mp
  exact (IsPullback.of_map_of_faithful Scheme.Spec h).unop

end FLT.Mazur.SpecCartesianAlgebraPushout
