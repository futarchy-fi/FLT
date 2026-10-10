/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXConicOverlapGeometry
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Retaining both affine lines when the divided conic constant vanishes

At c=0 each rational parameter open is the entire affine line. The two
ordered charts are disjoint and cover the original conic. These statements
use the full conic, not an open obtained by discarding a component.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type*) [CommRing R]

/-- When the divided constant vanishes the rational parameter algebra is the full line. -/
def conicZeroParameterEquiv : ConicParameterOpen (0 : R) ≃ₐ[R] R[X] :=
  ((IsLocalization.atUnit R[X] (ConicParameterOpen (0 : R))
    (conicParameterPolynomial (0 : R)) (by
      simp only [conicParameterPolynomial, map_zero, zero_mul, sub_zero, isUnit_one])).symm
        ).restrictScalars R

/-- The zero-constant parameter identification retains every polynomial function. -/
theorem conicZeroParameterEquiv_base (p : R[X]) :
    conicZeroParameterEquiv R (algebraMap R[X] (ConicParameterOpen (0 : R)) p) = p := by
  exact (IsLocalization.atUnit R[X] (ConicParameterOpen (0 : R))
    (conicParameterPolynomial (0 : R)) (by
      simp only [conicParameterPolynomial, map_zero, zero_mul, sub_zero,
        isUnit_one])).symm.commutes p

/-- The parameter coordinate remains the original polynomial variable. -/
theorem conicZeroParameterEquiv_z :
    conicZeroParameterEquiv R (conicParameterZ (0 : R)) = X :=
  conicZeroParameterEquiv_base R X

/-- The actual zero-constant parameter scheme is the entire affine line. -/
def conicZeroParameterIso : Spec (.of (ConicParameterOpen (0 : R))) ≅ Spec (.of R[X]) :=
  Scheme.Spec.mapIso (conicZeroParameterEquiv R).symm.toRingEquiv.toCommRingCatIso.op

variable {R} (a : R) (ha : IsUnit a)
local notation "i₁" =>
  Iso.inv (conicFirstParameterIso a 0 ha) ≫ conicFirstOpenImmersion a 0
local notation "i₂" =>
  Iso.inv (conicSecondParameterIso a 0 ha) ≫ conicSecondOpenImmersion a 0

/-- The explicit zero-constant overlap has no points. -/
theorem conicZeroOverlap_isEmpty : IsEmpty (Spec (.of (ConicParameterOverlap a (0 : R)))) := by
  exact PrimeSpectrum.isEmpty_iff_subsingleton.mpr (conicOverlap_zero_subsingleton a)

/-- The two full ordered parameter charts are disjoint when the divided constant vanishes. -/
theorem conicZeroParameters_disjoint : Disjoint (Set.range i₁) (Set.range i₂) := by
  apply Scheme.isEmpty_pullback_iff.mp
  let _ := conicZeroOverlap_isEmpty a
  exact (conicParameterOverlapIso a 0 ha).symm.hom.homeomorph.isEmpty

/-- Both zero-constant parameter charts together retain the whole conic. -/
theorem conicZeroParameters_cover : Set.range i₁ ∪ Set.range i₂ = Set.univ := by
  ext p
  simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
  rcases conicOpenImmersions_cover a 0 ha p with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · obtain ⟨s, hs⟩ := (conicFirstParameterIso a 0 ha).inv.homeomorph.surjective t
    exact Or.inl ⟨s, congrArg (conicFirstOpenImmersion a 0) hs⟩
  · obtain ⟨s, hs⟩ := (conicSecondParameterIso a 0 ha).inv.homeomorph.surjective t
    exact Or.inr ⟨s, congrArg (conicSecondOpenImmersion a 0) hs⟩

end FLT.Mazur.WeierstrassModificationX
