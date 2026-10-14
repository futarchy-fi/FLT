/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCoefficientJoin
public import FLT.Mazur.SchemeRelationInvariantAffineUniversal
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Actual joint affine models of a complete scheme relation

Two systems of invariant coefficients give a joint target with morphisms to
both original targets. All maps are constructed from actual regular functions;
no Cartesian square, flatness, or equality with the original relation is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationJointModel
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {E A : Scheme.{u}} (p q : E ⟶ A)
  {C D : Type u} [CommRing C] [CommRing D]
  (c : C →+* compatibleFunctions p q) (d : D →+* compatibleFunctions p q)

/-- A target built from both coefficient systems inside the original invariant functions. -/
def target : Scheme.{u} := Spec (.of (FiniteCoefficientJoin.algebra c d))

/-- The joint target maps to the first coefficient model. -/
def toLeft : target p q c d ⟶ Spec (.of C) :=
  Spec.map (CommRingCat.ofHom (FiniteCoefficientJoin.left c d))

/-- The independent second coefficient model is retained as well. -/
def toRight : target p q c d ⟶ Spec (.of D) :=
  Spec.map (CommRingCat.ofHom (FiniteCoefficientJoin.right c d))

/-- The full invariant target maps to the joint finite target. -/
def fromInvariants : SchemeRelationInvariantSpectrum.target p q ⟶ target p q c d :=
  Spec.map (CommRingCat.ofHom (FiniteCoefficientJoin.inclusion c d))

/-- The source projection keeps all original coefficient equations. -/
def projection : A ⟶ target p q c d :=
  SchemeRelationInvariantSpectrum.projection p q ≫ fromInvariants p q c d

/-- The actual projection associated to any invariant coefficient system. -/
def coefficientProjection (b : C →+* compatibleFunctions p q) : A ⟶ Spec (.of C) :=
  A.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ((compatibleFunctions p q).subtype.comp b))

@[reassoc]
theorem projection_toLeft : projection p q c d ≫ toLeft p q c d =
    coefficientProjection p q c := by
  simp only [projection, fromInvariants, toLeft, SchemeRelationInvariantSpectrum.projection,
    SchemeRelationInvariantSpectrum.inclusion, Category.assoc, ← Spec.map_comp]
  rfl

@[reassoc]
theorem projection_toRight : projection p q c d ≫ toRight p q c d =
    coefficientProjection p q d := by
  simp only [projection, fromInvariants, toRight, SchemeRelationInvariantSpectrum.projection,
    SchemeRelationInvariantSpectrum.inclusion, Category.assoc, ← Spec.map_comp]
  rfl

/-- The full original relation is coequalized as actual scheme morphisms. -/
@[reassoc]
theorem projection_condition : p ≫ projection p q c d = q ≫ projection p q c d := by
  rw [projection, ← Category.assoc, ← Category.assoc,
    SchemeRelationInvariantSpectrum.projection_condition]

/-- The joint target is affine by construction. -/
instance isAffine : IsAffine (target p q c d) := inferInstanceAs (IsAffine (Spec _))

/-- Finiteness of both coefficient systems proves Noetherianity of the joint target. -/
instance isNoetherian [Algebra.FiniteType ℤ C] [Algebra.FiniteType ℤ D] :
    IsNoetherian (target p q c d) := inferInstanceAs (IsNoetherian (Spec _))

/-- Adjoining coefficients preserves a kernel already detected by the second model. -/
theorem projection_test_iff {Z : Scheme.{u}} (x y : Z ⟶ A)
    (hd : x ≫ coefficientProjection p q d = y ≫ coefficientProjection p q d ↔
      x ≫ SchemeRelationInvariantSpectrum.projection p q =
        y ≫ SchemeRelationInvariantSpectrum.projection p q) :
    x ≫ projection p q c d = y ≫ projection p q c d ↔
      x ≫ SchemeRelationInvariantSpectrum.projection p q =
        y ≫ SchemeRelationInvariantSpectrum.projection p q := by
  constructor
  · intro h
    apply hd.mp
    simpa only [Category.assoc, projection_toRight] using
      congrArg (fun z ↦ z ≫ toRight p q c d) h
  · intro h
    exact congrArg (fun z ↦ z ≫ fromInvariants p q c d) h

end FLT.Mazur.SchemeRelationJointModel
