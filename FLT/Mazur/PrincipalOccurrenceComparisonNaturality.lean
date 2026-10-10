/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCrossTransitionCoordinates
public import FLT.Mazur.AffineScalarMapComposition

/-!
# Naturality of the concrete atlas comparison maps

Both actual cross-chart routes commute with refinement on the entire
ambient chart ring. These are the maps appearing in equation descent,
not a separate family of assumed-compatible coordinate maps.
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

variable (hy : ∀ i k, Function.Bijective (y.hom i k))

/-- Identified overlap embeddings retain the full ambient transition square. -/
@[reassoc] theorem principalOccurrenceOpenAt_transition {j : κ}
    (i : ι) (k : J i) (hk : dst i k = j) :
    principalOccurrenceOverlapTransition hxy j ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceOpenAt e y hy i k hk ≫ principalOccurrenceAmbientTransition hxy i := by
  subst j
  exact principalOccurrenceOpen_comm hx hy hxy i k

/-- The spectrum of the left algebra comparison is its defining geometric route. -/
theorem principalOccurrenceCrossComparisonLeftAlg_spec (i : ι) (k : J i)
    (hk : dst i k = dst p.1.val.1 p.2) :
    Spec.map (CommRingCat.ofHom
        (principalOccurrenceCrossComparisonLeftAlg e x hx p q i k hk).toRingHom) =
      (principalOccurrenceCrossIso x hx p q).inv ≫
        principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk :=
  AffineScalarMap.ofHom_spec _ _

/-- The spectrum of the right algebra comparison is its defining geometric route. -/
theorem principalOccurrenceCrossComparisonRightAlg_spec (i : ι) (l : J i)
    (hl : dst i l = dst q.1.val.1 q.2) :
    Spec.map (CommRingCat.ofHom
        (principalOccurrenceCrossComparisonRightAlg e x hx p q i l hl).toRingHom) =
      (principalOccurrenceCrossIso x hx p q).inv ≫
        principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl :=
  AffineScalarMap.ofHom_spec _ _

attribute [local irreducible] principalOccurrenceCrossComparisonLeftAlg
  principalOccurrenceCrossComparisonRightAlg principalOccurrenceCrossRingTransition
  principalOccurrenceCrossIso principalOccurrenceCrossOuterLeft principalOccurrenceCrossOuterRight
  principalOccurrenceCrossTransition principalOccurrenceOpenAt

/-- The actual left comparison commutes with the surjective ambient relation transition. -/
theorem principalOccurrenceCrossComparisonLeftAlg_natural (i : ι) (k : J i)
    (hk : dst i k = dst p.1.val.1 p.2) :
    (principalOccurrenceCrossRingTransition e x hxy p q).comp
        (principalOccurrenceCrossComparisonLeftAlg e x hx p q i k hk) =
      (principalOccurrenceCrossComparisonLeftAlg e y hy p q i k hk).comp
        (FiniteRelationModel.transition R (relationIdeal R (A i))
          (principalOccurrence_source_mono hxy i)) := by
  apply AffineScalarMap.spec_injective
  rw [AffineScalarMap.spec_comp, AffineScalarMap.spec_comp,
    principalOccurrenceCrossComparisonLeftAlg_spec,
    principalOccurrenceCrossComparisonLeftAlg_spec]
  rw [principalOccurrenceCrossRingTransition_coordinates_assoc e x hx hxy p q hy,
    Category.assoc, principalOccurrenceCrossTransition_left_assoc,
    principalOccurrenceOpenAt_transition e x hx hxy hy]
  simp only [Category.assoc]

/-- The actual right comparison obeys the same full ambient transition square. -/
theorem principalOccurrenceCrossComparisonRightAlg_natural (i : ι) (l : J i)
    (hl : dst i l = dst q.1.val.1 q.2) :
    (principalOccurrenceCrossRingTransition e x hxy p q).comp
        (principalOccurrenceCrossComparisonRightAlg e x hx p q i l hl) =
      (principalOccurrenceCrossComparisonRightAlg e y hy p q i l hl).comp
        (FiniteRelationModel.transition R (relationIdeal R (A i))
          (principalOccurrence_source_mono hxy i)) := by
  apply AffineScalarMap.spec_injective
  rw [AffineScalarMap.spec_comp, AffineScalarMap.spec_comp,
    principalOccurrenceCrossComparisonRightAlg_spec,
    principalOccurrenceCrossComparisonRightAlg_spec]
  rw [principalOccurrenceCrossRingTransition_coordinates_assoc e x hx hxy p q hy,
    Category.assoc, principalOccurrenceCrossTransition_right_assoc,
    principalOccurrenceOpenAt_transition e x hx hxy hy]
  simp only [Category.assoc]

end FLT.Mazur.FiniteTypeRelationModel
