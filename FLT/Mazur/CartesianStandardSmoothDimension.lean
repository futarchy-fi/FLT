/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCartesianSectionPushout
public import FLT.Mazur.SmoothFieldCotangentRank

/-!
# Detecting a standard chart's dimension on its actual cartesian fiber

One point of a nonempty affine fiber suffices to compute the dimension of a
standard-smooth chart. The coefficient maps and differential modules are
those of the original cartesian square.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.CartesianStandardSmoothDimension

open AffineCartesianSectionPushout

set_option backward.isDefEq.respectTransparency false

/-- A nonempty relative-dimension-d affine fiber determines its standard chart's dimension. -/
theorem of_isPullback (R S A : Type) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Algebra.IsStandardSmooth R A]
    {Y : Scheme} [IsAffine Y] (i : Y ⟶ Spec (.of A)) (g : Y ⟶ Spec (.of S))
    (h : IsPullback i g (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (d : ℕ) [SmoothOfRelativeDimension d g] (y : Y) :
    Algebra.IsStandardSmoothOfRelativeDimension d R A := by
  let C := Γ(Y, ⊤)
  let _ : Algebra A C := (scalars i).toAlgebra
  let _ : Algebra S C := (scalars g).toAlgebra
  let _ : Algebra R C := ((scalars i).comp (algebraMap R A)).toAlgebra
  have hp := isPushout_spec i g (algebraMap R A) (algebraMap R S) h
  let _ : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' (by
    exact congrArg CommRingCat.Hom.hom hp.w.symm)
  let _ : Algebra.IsPushout R S A C := CommRingCat.isPushout_iff_isPushout.mp hp
  let p := (Y.isoSpec.hom y).asIdeal
  let B := p.ResidueField
  let _ : Algebra A B := ((algebraMap C B).comp (algebraMap A C)).toAlgebra
  let _ : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq' rfl
  have hg : SmoothOfRelativeDimension d (Y.isoSpec.inv ≫ g) :=
    IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension d) inferInstance Y.isoSpec.inv
  rw [fromSpec_toBase, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)] at hg
  exact SmoothFieldCotangentRank.relativeDimension_of_baseChange R S A C B d hg

end FLT.Mazur.CartesianStandardSmoothDimension
