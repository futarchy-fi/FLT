/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOriginalPatches
public import FLT.Mazur.PrincipalOccurrenceCrossChartIntersections

/-!
# Recovery of cross-chart comparison domains

Original patches from different charts intersect over the actual original
shared overlap. Their canonical map to the finite intersection recovers both
outer overlap labels.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))



/-- Original restrictions are open immersions. -/
instance principalOccurrenceOriginalRestriction_isOpenImmersion (i : ι) (k : J i) {r : A i}
    (h : PrimeSpectrum.basicOpen r ≤ PrimeSpectrum.basicOpen (a i k)) :
    IsOpenImmersion (principalOccurrenceOriginalRestriction e i k h) := by
  dsimp only [principalOccurrenceOriginalRestriction]
  infer_instance

/-- An original patch is open in its shared overlap. -/
instance principalOccurrenceOriginalPatchOpen_isOpenImmersion {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    IsOpenImmersion (principalOccurrenceOriginalPatchOpen e p) := by
  obtain ⟨⟨⟨i, k⟩, rfl⟩, l⟩ := p
  dsimp only [principalOccurrenceOriginalPatchOpen]
  infer_instance

variable {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)

/-- The original comparison domain, allowing different ambient charts and outer labels. -/
abbrev principalOccurrenceOriginalCross : Scheme.{u} :=
  pullback (principalOccurrenceOriginalPatchOpen e p) (principalOccurrenceOriginalPatchOpen e q)

/-- The original common intersection maps into its shared overlap. -/
def principalOccurrenceOriginalCrossOpen :
    principalOccurrenceOriginalCross e p q ⟶ Spec (.of (Localization.Away (b j))) :=
  pullback.fst _ _ ≫ principalOccurrenceOriginalPatchOpen e p

/-- Its shared-overlap map is an open immersion. -/
instance principalOccurrenceOriginalCrossOpen_isOpenImmersion :
    IsOpenImmersion (principalOccurrenceOriginalCrossOpen e p q) := by
  dsimp only [principalOccurrenceOriginalCrossOpen]
  infer_instance

/-- The first outer-label restriction on the original intersection. -/
def principalOccurrenceOriginalCrossOuterLeft :
    principalOccurrenceOriginalCross e p q ⟶
      Spec (.of (Localization.Away (b (dst p.1.val.1 p.2)))) :=
  pullback.fst _ _ ≫ principalOccurrenceOriginalPatchOther e p

/-- The second outer-label restriction on the original intersection. -/
def principalOccurrenceOriginalCrossOuterRight :
    principalOccurrenceOriginalCross e p q ⟶
      Spec (.of (Localization.Away (b (dst q.1.val.1 q.2)))) :=
  pullback.snd _ _ ≫ principalOccurrenceOriginalPatchOther e q

variable [∀ i, Algebra.FiniteType R (A i)] [∀ j, Algebra.FiniteType R (B j)]
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))

/-- The two original patch projections induce the finite cross-chart projection. -/
def principalOccurrenceOriginalCrossProjection :
    principalOccurrenceOriginalCross e p q ⟶ principalOccurrenceCross x hx p q :=
  pullback.lift
    (pullback.fst _ _ ≫ principalOccurrenceOriginalPatchProjection e x hx p)
    (pullback.snd _ _ ≫ principalOccurrenceOriginalPatchProjection e x hx q) (by
      simp only [Category.assoc, principalOccurrenceOriginalPatchProjection_left]
      exact pullback.condition_assoc _)

/-- The finite comparison recovers the entire map into the shared overlap. -/
@[reassoc (attr := simp)] theorem principalOccurrenceOriginalCrossProjection_open :
    principalOccurrenceOriginalCrossProjection e p q x hx ≫ principalOccurrenceCrossOpen x hx p q =
      principalOccurrenceOriginalCrossOpen e p q ≫
        principalOccurrenceOverlapProjection e x j := by
  simp only [principalOccurrenceOriginalCrossProjection, principalOccurrenceCrossOpen,
    principalOccurrenceCrossLeft, pullback.lift_fst_assoc,
    principalOccurrenceOriginalPatchProjection_left, Category.assoc,
    principalOccurrenceOriginalCrossOpen]

/-- The finite left outer map recovers the actual original outer map. -/
@[reassoc (attr := simp)] theorem principalOccurrenceOriginalCrossProjection_left :
    principalOccurrenceOriginalCrossProjection e p q x hx ≫
        principalOccurrenceCrossOuterLeft x hx p q =
      principalOccurrenceOriginalCrossOuterLeft e p q ≫
        principalOccurrenceOverlapProjection e x (dst p.1.val.1 p.2) := by
  simp only [principalOccurrenceOriginalCrossProjection, principalOccurrenceCrossOuterLeft,
    principalOccurrenceCrossLeft, pullback.lift_fst_assoc,
    principalOccurrenceOriginalPatchProjection_right, Category.assoc,
    principalOccurrenceOriginalCrossOuterLeft]

/-- The finite right outer map recovers the actual original outer map. -/
@[reassoc (attr := simp)] theorem principalOccurrenceOriginalCrossProjection_right :
    principalOccurrenceOriginalCrossProjection e p q x hx ≫
        principalOccurrenceCrossOuterRight x hx p q =
      principalOccurrenceOriginalCrossOuterRight e p q ≫
        principalOccurrenceOverlapProjection e x (dst q.1.val.1 q.2) := by
  simp only [principalOccurrenceOriginalCrossProjection, principalOccurrenceCrossOuterRight,
    principalOccurrenceCrossRight, pullback.lift_snd_assoc,
    principalOccurrenceOriginalPatchProjection_right, Category.assoc,
    principalOccurrenceOriginalCrossOuterRight]

end FLT.Mazur.FiniteTypeRelationModel
