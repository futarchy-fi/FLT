/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXBaseChange
public import FLT.Mazur.WeierstrassSuccessiveXFlat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flat finitely presented structure maps of full successive tensor charts

The two displayed relations give finite presentation. Flatness of the original
chart passes to every coefficient extension, including arithmetic quotients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- The displayed pair of equations finitely presents the original successive chart. -/
instance successiveCoordinate_finitePresentation :
    Algebra.FinitePresentation R (Coordinate W s π b3 b4 b6) :=
  Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.toFinite _))

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Scalar extension retains the finite presentation of the whole successive chart. -/
instance successiveScalarExtension_finitePresentation :
    Algebra.FinitePresentation S (ScalarExtension W s π b3 b4 b6 S) :=
  inferInstanceAs (Algebra.FinitePresentation S (S ⊗[R] Coordinate W s π b3 b4 b6))

/-- The actual tensor chart structure map is locally of finite presentation. -/
instance successiveTensorStructure_finitePresentation :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom
      (algebraMap S (ScalarExtension W s π b3 b4 b6 S)))) :=
  (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr inferInstance)

variable [IsDomain R] [IsBezout R]

/-- Nonzero original parameter gives a flat structure map after arbitrary scalar extension. -/
theorem successiveTensorStructure_flat (hπ : π ≠ 0) :
    Flat (Spec.map (CommRingCat.ofHom
      (algebraMap S (ScalarExtension W s π b3 b4 b6 S)))) := by
  let _ := coordinate_flat_of_parameter_ne_zero W s π b3 b4 b6 hπ
  let _ : Module.Flat S (ScalarExtension W s π b3 b4 b6 S) :=
    inferInstanceAs (Module.Flat S (S ⊗[R] Coordinate W s π b3 b4 b6))
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

end FLT.Mazur.WeierstrassSuccessiveX
