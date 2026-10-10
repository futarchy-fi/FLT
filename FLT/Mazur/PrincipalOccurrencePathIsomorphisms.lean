/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceSurjective
public import FLT.Mazur.PrincipalFanPathIsomorphisms

/-!
# Isomorphisms with multiply incident overlap targets

Apply exact kernel patching separately at each ambient source chart while
retaining every overlap target literally. The resulting coordinate maps are
isomorphisms even when a target receives several distinct incoming charts.
The required target restrictions and their ambient path equations are explicit.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  [∀ i, Finite (J i)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}

/-- Compatible actual restriction paths produce simultaneous shared-target isomorphisms. -/
theorem exists_principalOccurrence_bijective_of_paths
    (hf : ∀ i e, Function.Injective (f i e)) (x : PrincipalOccurrenceStage dst a b f)
    (hx : ∀ i e, Function.Surjective (x.hom i e))
    (ρ : ∀ i e e', PrincipalStage R (B (dst i e)) (b (dst i e)) (x.target (dst i e)) →+*
      PrincipalFanRestrictionTarget (principalOccurrenceFan x i) e e')
    (hρ : ∀ i, PrincipalFanRestrictionEquations (principalOccurrenceFan x i) (ρ i)) :
    ∃ y : PrincipalOccurrenceStage dst a b f, x ≤ y ∧ y.target = x.target ∧
      ∀ i e, Function.Bijective (y.hom i e) := by
  choose q hq d hd hfac using fun i ↦
    exists_principalFan_equivs_of_paths (R := R) (A := A i)
      (B := fun e ↦ B (dst i e)) (a := a i) (b := fun e ↦ b (dst i e))
      (hf i) (principalOccurrenceFan x i) (hx i) (ρ i) (hρ i)
  let y : PrincipalOccurrenceStage dst a b f :=
    ⟨q, x.target, fun i e ↦ (d i e).toAlgHom, hfac⟩
  refine ⟨y, ⟨hq, le_rfl, fun i e ↦ ?_⟩, rfl, fun i e ↦ (d i e).bijective⟩
  change (d i e).toAlgHom.comp (principalTransition (a i e) (hq i)) =
    (principalTransition (b (dst i e)) (le_refl (x.target (dst i e)))).comp (x.hom i e)
  rw [principalTransition_refl, AlgHom.id_comp]
  exact hd i e

end FLT.Mazur.FiniteTypeRelationModel
