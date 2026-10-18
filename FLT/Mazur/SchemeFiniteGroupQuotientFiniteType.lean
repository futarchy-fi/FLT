/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupQuotient
public import FLT.Mazur.FiniteGroupQuotientFinite
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Finite type of actual affine invariant quotients over the integers

Finiteness of the original coordinate algebra over its invariant subring and
Artin--Tate prove finite type of the invariant ring. This concerns the quotient
target over the integers, as well as the already finite quotient morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {G : Type} [Group G] [Finite G] {X : Scheme} [IsAffine X]
  (ρ : G →* Aut X)

omit [Finite G] [IsAffine X] in
/-- Artin--Tate makes the actual invariant ring a finite type integer algebra. -/
theorem invariantCoordinates_finiteType [Algebra.FiniteType ℤ Γ(X, ⊤)] [Finite G] :
    Algebra.FiniteType ℤ (invariantCoordinates ρ) := by
  let _ := SchemeCoordinateAction.coordinateAction ρ
  have h := FiniteGroupQuotient.inclusion_finite G Γ(X, ⊤) ℤ
  let _ : Module.Finite (invariantCoordinates ρ) Γ(X, ⊤) := h
  exact ⟨fg_of_fg_of_fg ℤ (invariantCoordinates ρ) Γ(X, ⊤)
    Algebra.FiniteType.out Module.Finite.fg_top
    (FiniteGroupQuotient.inclusion_injective G Γ(X, ⊤))⟩

omit [Finite G] in
/-- The coordinates of an actual affine finite type integer scheme are finite type. -/
theorem integerCoordinates_finiteType (f : X ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] :
    Algebra.FiniteType ℤ Γ(X, ⊤) := by
  have h : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ Γ(X, ⊤)))) := by
    have he : Spec.map (CommRingCat.ofHom (algebraMap ℤ Γ(X, ⊤))) =
        X.isoSpec.inv ≫ f := specZIsTerminal.hom_ext _ _
    rw [he]
    infer_instance
  exact RingHom.finiteType_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h)

/-- The integer structure map on the actual invariant-coordinate spectrum. -/
def quotientToInt : quotient ρ ⟶ Spec (.of ℤ) := specZIsTerminal.from _

include ρ in
/-- Finite type descends from the original affine scheme to its finite-group quotient. -/
theorem quotientToInt_locallyOfFiniteType (f : X ⟶ Spec (.of ℤ)) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (quotientToInt ρ) := by
  let _ := integerCoordinates_finiteType f
  let _ := invariantCoordinates_finiteType ρ
  have he : quotientToInt ρ =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (invariantCoordinates ρ))) :=
    specZIsTerminal.hom_ext _ _
  rw [he]
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- The invariant spectrum is affine and hence quasi-compact over the integers. -/
instance quotientToInt_quasiCompact : QuasiCompact (quotientToInt ρ) := by
  unfold quotientToInt quotient
  infer_instance

end FLT.Mazur.SchemeFiniteGroupQuotient
