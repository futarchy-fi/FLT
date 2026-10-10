/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceComparisonScalars
public import FLT.Mazur.PrincipalOccurrenceCrossEquationRefinement

/-!
# Actual comparison maps in the equation-descent local coordinates

The initial iterated-localization coordinates give the same quotient map
as the actual cross-chart coordinates. Thus atlas compatibility supplies
the original equality required by the finite local-equation theorem.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalQuotientEquiv
  FiniteRelationIterated.toQuotient FiniteRelationLocalization.toQuotient
  FiniteRelationIterated.transition FiniteRelationLocalization.transition
  principalOccurrenceCrossRefinedEquiv

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))


variable {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)




/-- The initial iterated localization and actual cross-chart coordinates have the same quotient. -/
theorem principalOccurrenceCross_initial_quotient :
    (FiniteRelationIterated.toQuotient R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j)
      (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)
      ⟨x.target j, le_refl (x.target j)⟩).comp
        (principalOccurrenceCrossRefinedEquiv x p q le_rfl).symm.toAlgHom =
      principalOccurrenceCrossToQuotient e x p q := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers (principalOccurrencePatchDenominator x p *
      principalOccurrencePatchDenominator x q))
  apply AlgHom.ext
  intro z
  have he : (principalOccurrenceCrossRefinedEquiv x p q le_rfl).symm
      (algebraMap _ (PrincipalOccurrenceCrossRing x p q) z) = algebraMap _ _ z := by
    apply (principalOccurrenceCrossRefinedEquiv x p q le_rfl).injective
    rw [AlgEquiv.apply_symm_apply, principalOccurrenceCrossRefinedEquiv_algebraMap]
  change FiniteRelationIterated.toQuotient R (relationIdeal R (B j))
    (principalRepresentative R (B j) (b j)) (x.target j) _ ⟨x.target j, le_refl (x.target j)⟩
      ((principalOccurrenceCrossRefinedEquiv x p q le_rfl).symm (algebraMap _ _ z)) = _
  rw [he, FiniteRelationIterated.toQuotient_algebraMap]
  exact (principalOccurrenceCrossToQuotient_algebraMap e x p q z).symm

/-- The actual left comparison expressed in the fixed-denominator local model. -/
def principalOccurrenceLocalComparisonLeft (i : ι) (k : J i)
    (hk : dst i k = dst p.1.val.1 p.2) :
    Stage R (A i) (x.source i) →ₐ[R] principalOccurrenceLocalStage e x j
      (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)
      ⟨x.target j, le_refl (x.target j)⟩ :=
  (principalOccurrenceCrossRefinedEquiv x p q le_rfl).symm.toAlgHom.comp
    (principalOccurrenceCrossComparisonLeftAlg e x hx p q i k hk)

/-- The actual right comparison expressed in the same local model. -/
def principalOccurrenceLocalComparisonRight (i : ι) (l : J i)
    (hl : dst i l = dst q.1.val.1 q.2) :
    Stage R (A i) (x.source i) →ₐ[R] principalOccurrenceLocalStage e x j
      (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)
      ⟨x.target j, le_refl (x.target j)⟩ :=
  (principalOccurrenceCrossRefinedEquiv x p q le_rfl).symm.toAlgHom.comp
    (principalOccurrenceCrossComparisonRightAlg e x hx p q i l hl)

variable {X : Scheme.{u}} (U : ∀ i, Spec (.of (A i)) ⟶ X)
  (V : ∀ j, Spec (.of (Localization.Away (b j))) ⟶ X)
  (hUV : ∀ i k, principalOccurrenceOriginalOpen e i k ≫ U i = V (dst i k))

include hUV in
/-- Original atlas incidence proves the full quotient equation in the local descent coordinates. -/
theorem principalOccurrenceLocalComparison_quotient (i : ι) [Mono (U i)]
    (k l : J i) (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2) :
    (FiniteRelationIterated.toQuotient R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j)
      (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)
      ⟨x.target j, le_refl (x.target j)⟩).comp
        (principalOccurrenceLocalComparisonLeft e x hx p q i k hk) =
    (FiniteRelationIterated.toQuotient R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j)
      (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q)
      ⟨x.target j, le_refl (x.target j)⟩).comp
        (principalOccurrenceLocalComparisonRight e x hx p q i l hl) := by
  simp only [principalOccurrenceLocalComparisonLeft, principalOccurrenceLocalComparisonRight,
    ← AlgHom.comp_assoc, principalOccurrenceCross_initial_quotient]
  apply AlgHom.coe_ringHom_injective
  exact principalOccurrenceCrossComparison_quotient e x hx p q U V hUV i k l hk hl

end FLT.Mazur.FiniteTypeRelationModel
