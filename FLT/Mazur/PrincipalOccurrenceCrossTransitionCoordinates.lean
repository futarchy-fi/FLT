/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceAtlasEquationRefinement
public import FLT.Mazur.PrincipalOccurrenceCrossNaturality

/-!
# Actual cross-chart coordinates under refinement

The transport used by equation descent induces the canonical map between
the actual localized coordinate rings. Its spectrum agrees with the
geometric cross-chart transition, including the coordinate isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalQuotientEquiv
  FiniteRelationIterated.toQuotient FiniteRelationLocalization.toQuotient
  FiniteRelationIterated.transition FiniteRelationLocalization.transition
  principalOccurrenceCrossRefinedEquiv
  principalOccurrenceLocalComparisonLeft principalOccurrenceLocalComparisonRight

universe u v w z z'

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))



variable {y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)}
  (hxy : x ≤ y) {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)

/-- The equation transport on actual, rather than fixed-denominator, cross-chart coordinates. -/
def principalOccurrenceCrossRingTransition :
    PrincipalOccurrenceCrossRing x p q →ₐ[R] PrincipalOccurrenceCrossRing y p q :=
  (principalOccurrenceCrossEquationTransport e x hxy p q).comp
    (principalOccurrenceCrossRefinedEquiv x p q le_rfl).symm.toAlgHom

/-- The inverse initial coordinate identification fixes every numerator. -/
theorem principalOccurrenceCrossInitial_symm_algebraMap
    (z : PrincipalStage R (B j) (b j) (x.target j)) :
    (principalOccurrenceCrossRefinedEquiv x p q le_rfl).symm
        (algebraMap _ (PrincipalOccurrenceCrossRing x p q) z) = algebraMap _ _ z := by
  apply (principalOccurrenceCrossRefinedEquiv x p q le_rfl).injective
  rw [AlgEquiv.apply_symm_apply, principalOccurrenceCrossRefinedEquiv_algebraMap]

/-- Actual cross-chart transitions act on numerators by the overlap transition. -/
theorem principalOccurrenceCrossRingTransition_algebraMap
    (z : PrincipalStage R (B j) (b j) (x.target j)) :
    principalOccurrenceCrossRingTransition e x hxy p q (algebraMap _ _ z) =
      algebraMap _ (PrincipalOccurrenceCrossRing y p q)
        (principalTransition (b j) (principalOccurrence_target_mono hxy j) z) := by
  change principalOccurrenceCrossRefinedEquiv x p q hxy
    (FiniteRelationIterated.transition R (relationIdeal R (B j))
      (principalRepresentative R (B j) (b j)) (x.target j) _
      (show (⟨x.target j, le_refl (x.target j)⟩ : Set.Ici (x.target j)) ≤
        ⟨y.target j, principalOccurrence_target_mono hxy j⟩ from
          principalOccurrence_target_mono hxy j)
      ((principalOccurrenceCrossRefinedEquiv x p q le_rfl).symm (algebraMap _ _ z))) = _
  rw [principalOccurrenceCrossInitial_symm_algebraMap,
    FiniteRelationIterated.transition_algebraMap,
    principalOccurrenceCrossRefinedEquiv_algebraMap]

/-- The coordinate transition preserves the principal inclusion into the shared overlap. -/
@[reassoc] theorem principalOccurrenceCrossRingTransition_inclusion :
    Spec.map (CommRingCat.ofHom
        (principalOccurrenceCrossRingTransition e x hxy p q).toRingHom) ≫
      PrincipalLocalizationSquare.inclusion
        (principalOccurrencePatchDenominator x p * principalOccurrencePatchDenominator x q) =
    PrincipalLocalizationSquare.inclusion
        (principalOccurrencePatchDenominator y p * principalOccurrencePatchDenominator y q) ≫
      principalOccurrenceOverlapTransition hxy j := by
  simp only [PrincipalLocalizationSquare.inclusion, principalOccurrenceOverlapTransition,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact principalOccurrenceCrossRingTransition_algebraMap e x hxy p q z

/-- Equation transport is the actual geometric transition in cross-chart coordinates. -/
@[reassoc] theorem principalOccurrenceCrossRingTransition_coordinates
    (hy : ∀ i k, Function.Bijective (y.hom i k)) :
    Spec.map (CommRingCat.ofHom
        (principalOccurrenceCrossRingTransition e x hxy p q).toRingHom) ≫
        (principalOccurrenceCrossIso x hx p q).inv =
      (principalOccurrenceCrossIso y hy p q).inv ≫
        principalOccurrenceCrossTransition hxy hx hy p q := by
  apply (cancel_mono (principalOccurrenceCrossOpen x hx p q)).mp
  simp only [Category.assoc, principalOccurrenceCrossTransition_open]
  rw [← principalOccurrenceCrossIso_fac x hx p q,
    ← principalOccurrenceCrossIso_fac y hy p q]
  simp only [Iso.inv_hom_id, Category.id_comp, ← Category.assoc]
  exact principalOccurrenceCrossRingTransition_inclusion e x hxy p q

end FLT.Mazur.FiniteTypeRelationModel
