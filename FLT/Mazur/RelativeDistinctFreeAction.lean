/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDistinctTuples
public import FLT.Mazur.SchemeFiniteGroupFreeBoundary

/-!
# Freeness of the constructed ordered-point action

A permutation fixing a nonempty scheme-valued tuple fixes every label, since
all original coordinate maps remain distinct. This proves geometric freeness
and hence invariant boundary lifting on affine ordered-point schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme} (E : Over S) [IsSeparated E.hom] (I : Type) [Fintype I]

/-- Distinct coordinate maps remain injectively labeled after forgetting the base. -/
theorem distinctCoordinate_left_injective {T : Scheme} [Nonempty T]
    (a : T ⟶ (distinctScheme E I).left) :
    Function.Injective (fun i ↦ a ≫ (distinctCoordinate E I i).left) := by
  let T' : Over S := Over.mk (a ≫ (distinctScheme E I).hom)
  let a' : T' ⟶ distinctScheme E I := Over.homMk a rfl
  let _ : Nonempty T'.left := ‹Nonempty T›
  intro i j h
  apply distinctCoordinate_injective E I a'
  exact Over.OverMorphism.ext h

/-- No nonidentity permutation fixes a tuple on any nonempty test scheme. -/
theorem distinctAction_free {T : Scheme} [Nonempty T]
    (a : T ⟶ (distinctScheme E I).left) (e : Equiv.Perm I)
    (he : a ≫ (distinctAction E I e).hom = a) : e = 1 := by
  apply Equiv.ext
  intro i
  have h := congrArg (fun b ↦ b ≫ (distinctCoordinate E I (e i)).left) he
  rw [Category.assoc, distinctAction_coordinate, e.symm_apply_apply] at h
  exact (distinctCoordinate_left_injective E I a h).symm

/-- Field-valued freeness is proved for the actual constructed open scheme. -/
theorem distinctAction_field_free (K : Type) [Field K]
    (a : Spec (.of K) ⟶ (distinctScheme E I).left) (e : Equiv.Perm I)
    (he : a ≫ (distinctAction E I e).hom = a) : e = 1 :=
  distinctAction_free E I a e he

variable [IsAffine (distinctScheme E I).left]
  {B : Scheme} (ρ : Equiv.Perm I →* Aut B) (i : B ⟶ (distinctScheme E I).left)
  [IsClosedImmersion i]
  (hi : ∀ e : Equiv.Perm I, (ρ e).hom ≫ i = i ≫ (distinctAction E I e).hom)

/-- Every invariant section on an equivariant closed boundary has an actual invariant lift. -/
theorem distinct_invariantMap_surjective :
    Function.Surjective (SchemeFiniteGroupQuotient.invariantMap ρ (distinctAction E I) i hi) :=
  SchemeFiniteGroupQuotient.invariantMap_surjective_of_free (distinctAction E I)
    (distinctAction_field_free E I) ρ i hi

/-- The actual quotient map of an equivariant ordered-point boundary is a closed immersion. -/
theorem distinct_quotientHom_closed :
    IsClosedImmersion (SchemeFiniteGroupQuotient.quotientHom ρ (distinctAction E I) i hi) :=
  SchemeFiniteGroupQuotient.quotientHom_isClosedImmersion_of_free (distinctAction E I)
    (distinctAction_field_free E I) ρ i hi

end FLT.Mazur.RelativeOrderedTuples
