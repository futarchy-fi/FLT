/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedDegreeZero
public import FLT.Mazur.IdealAdicGradedRing

/-!
# Closed structure scalars in the actual total graded algebra

On an ambient affine chart the degree-zero comparison gives a canonical
algebra structure over the coordinate ring of the actual closed chart.
The map retains the original graded unit after the actual quotient map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient

universe u

namespace FLT.Mazur.IdealAdicGradedSections

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- The ring of the actual closed inverse image of an ambient open. -/
abbrev ClosedScalars (U : X.Opens) := Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U)

/-- Degree-zero sections identify with sections of the actual closed structure sheaf. -/
def zeroSectionEquiv (U : X.Opens) : Piece I U 0 ≃+ ClosedScalars I U :=
  ((SheafOfModules.evaluation X.ringCatSheaf (.op U)).mapIso
    (idealGradedZeroIso I)).toLinearEquiv.toAddEquiv

omit [IsLocallyNoetherian X] in
/-- The degree-zero identification preserves the actual quotient of each scalar. -/
lemma zeroSectionEquiv_scalar (U : X.Opens) (r : Γ(X, U)) :
    zeroSectionEquiv I U (scalar I U r) = I.subschemeι.app U r :=
  congrArg (fun k ↦ k.app U r) (idealGradedUnit_zeroIso I)

/-- Closed structure sections embed additively in degree zero of the total graded algebra. -/
def closedScalarAdd (U : X.Opens) : ClosedScalars I U →+ Sections I U :=
  (of I U 0).toAddMonoidHom.comp (zeroSectionEquiv I U).symm.toAddMonoidHom

/-- Closed scalar inclusion retains the original graded algebra map. -/
lemma closedScalarAdd_quotient (U : X.Opens) (r : Γ(X, U)) :
    closedScalarAdd I U (I.subschemeι.app U r) = algebraMap Γ(X, U) (Sections I U) r := by
  change of I U 0 ((zeroSectionEquiv I U).symm (I.subschemeι.app U r)) =
    of I U 0 (scalar I U r)
  congr 1
  exact (AddEquiv.symm_apply_eq _).mpr (zeroSectionEquiv_scalar I U r).symm

/-- The closed scalar inclusion is unital and multiplicative on every ambient affine chart. -/
def closedScalarRingHom (U : X.affineOpens) : ClosedScalars I U.1 →+* Sections I U.1 where
  __ := closedScalarAdd I U.1
  map_one' := by
    change closedScalarAdd I U.1 1 = 1
    rw [← map_one (I.subschemeι.app U.1).hom, closedScalarAdd_quotient, map_one]
  map_mul' a b := by
    obtain ⟨r, rfl⟩ := idealQuotientMap_affine_surjective I U a
    obtain ⟨s, rfl⟩ := idealQuotientMap_affine_surjective I U b
    change closedScalarAdd I U.1 (I.subschemeι.app U.1 r * I.subschemeι.app U.1 s) =
      closedScalarAdd I U.1 (I.subschemeι.app U.1 r) *
        closedScalarAdd I U.1 (I.subschemeι.app U.1 s)
    rw [← map_mul, closedScalarAdd_quotient, closedScalarAdd_quotient,
      closedScalarAdd_quotient, map_mul]

/-- The actual total coefficient algebra has its closed structure scalar action. -/
@[instance_reducible]
def closedScalarAlgebra (U : X.affineOpens) : Algebra (ClosedScalars I U.1) (Sections I U.1) :=
  (closedScalarRingHom I U).toAlgebra

/-- The closed scalar map has exactly the entire degree-zero coefficient as its image. -/
lemma closedScalarAdd_range (U : X.Opens) :
    Set.range (closedScalarAdd I U) = Set.range (of I U 0) := by
  ext t
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨(zeroSectionEquiv I U).symm r, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨zeroSectionEquiv I U s, by
      change of I U 0 ((zeroSectionEquiv I U).symm (zeroSectionEquiv I U s)) = _
      rw [AddEquiv.symm_apply_apply]⟩

end FLT.Mazur.IdealAdicGradedSections
