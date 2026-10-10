/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanRefinedRestrictionPaths
public import FLT.Mazur.PrincipalOccurrencePathIsomorphisms

/-!
# Occurrence isomorphisms from literal refined restrictions

Accept restrictions whose source and target use the same refined ambient
stages. Full path equations are proved from their old ambient equations,
then exact kernel patching refines the coordinates to bijections while
preserving every shared overlap target.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

section Fan

variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
  [Algebra.FiniteType R C] {τ : Type v}
  {D : τ → Type u} [∀ i, CommRing (D i)] [∀ i, Algebra R (D i)]
  [∀ i, Algebra.FiniteType R (D i)] {c : τ → C} {d : ∀ i, D i}
  {g : ∀ i, Localization.Away (c i) →ₐ[R] Localization.Away (d i)}
  {x y : PrincipalFanStage c d g}

/-- Include the refined chart ring into the literal old-coordinate restriction target. -/
def principalFanOldRestrictionInclusion (h : x ≤ y) (i j : τ) :
    PrincipalStage R (D j) (d j) (y.target j) →ₐ[R] PrincipalFanOldRestrictionTarget h i j :=
  Algebra.algHom R _ _

end Fan

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  [∀ i, Finite (J i)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}

/-- Literal refined restrictions produce shared-target bijections through full path equations. -/
theorem exists_principalOccurrence_bijective_of_refined_restrictions
    (hf : ∀ i e, Function.Injective (f i e))
    {x y : PrincipalOccurrenceStage dst a b f} (hxy : x ≤ y)
    (hy : ∀ i e, Function.Surjective (y.hom i e))
    (ρ : ∀ i e e', PrincipalStage R (B (dst i e)) (b (dst i e)) (y.target (dst i e)) →ₐ[R]
      PrincipalFanOldRestrictionTarget (principalOccurrenceFan_mono hxy i) e e')
    (hρ : ∀ i e e',
      ((ρ i e e').comp (principalTransition (b (dst i e))
        (principalOccurrence_target_mono hxy (dst i e)))).comp
          (principalFanAmbient (principalOccurrenceFan x i) e) =
      (principalFanOldRestrictionInclusion (principalOccurrenceFan_mono hxy i) e e').comp
        ((principalTransition (b (dst i e'))
          (principalOccurrence_target_mono hxy (dst i e'))).comp
            (principalFanAmbient (principalOccurrenceFan x i) e'))) :
    ∃ z : PrincipalOccurrenceStage dst a b f, y ≤ z ∧ z.target = y.target ∧
      ∀ i e, Function.Bijective (z.hom i e) := by
  let σ (i) (e e' : J i) := principalFanRefinedRestriction
    (principalOccurrenceFan_mono hxy i) e e' (ρ i e e')
  have hσ (i) : PrincipalFanRestrictionEquations (principalOccurrenceFan y i)
      (fun e e' ↦ (σ i e e').toRingHom) :=
    principalFanRefinedRestriction_equations (principalOccurrenceFan_mono hxy i) (ρ i) (hρ i)
  exact exists_principalOccurrence_bijective_of_paths hf y hy
    (fun i e e' ↦ (σ i e e').toRingHom) hσ

end FLT.Mazur.FiniteTypeRelationModel
