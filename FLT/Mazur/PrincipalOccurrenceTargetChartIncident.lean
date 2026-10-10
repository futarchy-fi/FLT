/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceTargetChartRecovery
public import FLT.Mazur.PrincipalOccurrencePatchGluing

/-!
# Glued maps into incident ambient charts

When the target chart contains a literal occurrence of the overlap, the
existing constrained patch family contains that occurrence's diagonal patch.
Its restriction identifies the glued map with the actual occurrence open
immersion and proves its full cartesian recovery square.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

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
  {j : κ} (i : ι)
  (hc : (⨆ p : PrincipalOccurrencePatchTo (dst := dst) j i,
    (principalOccurrencePatchOpen x hx p.1).opensRange) = ⊤)
  (he : ∀ p q : PrincipalOccurrencePatchTo (dst := dst) j i,
    principalOccurrenceCrossOuterLeft x hx p.1 q.1 ≫
        principalOccurrenceOpenAt e x hx i p.2.val p.2.property =
      principalOccurrenceCrossOuterRight x hx p.1 q.1 ≫
        principalOccurrenceOpenAt e x hx i q.2.val q.2.property)

attribute [local irreducible] principalOccurrenceTargetChartGlue

/-- Gluing into an incident chart recovers its actual occurrence map already at this stage. -/
theorem principalOccurrenceTargetChartGlue_eq_open (k : J i) (hk : dst i k = j) :
    principalOccurrenceTargetChartGlue e x hx i hc he =
      principalOccurrenceOpenAt e x hx i k hk := by
  subst j
  let p : PrincipalOccurrencePatchTo (dst := dst) (dst i k) i :=
    ⟨⟨⟨⟨i, k⟩, rfl⟩, k⟩, ⟨k, rfl⟩⟩
  apply (cancel_epi (principalOccurrencePatchOpen x hx p.1)).mp
  rw [principalOccurrenceTargetChartGlue_fac]
  change principalOccurrencePatchOther x hx p.1 ≫ principalOccurrenceOpen x hx i k =
    principalOccurrencePatchOpen x hx p.1 ≫ principalOccurrenceOpen x hx i k
  exact (principalOccurrencePatch_isPullback x hx i k k).w.symm

/-- The glued map into any incident chart is an open immersion. -/
theorem principalOccurrenceTargetChartGlue_isOpenImmersion (k : J i) (hk : dst i k = j) :
    IsOpenImmersion (principalOccurrenceTargetChartGlue e x hx i hc he) := by
  rw [principalOccurrenceTargetChartGlue_eq_open e x hx i hc he k hk]
  subst j
  exact principalOccurrenceOpen_isOpenImmersion x hx i k

/-- The incident target map has the entire original occurrence square as its base change. -/
theorem principalOccurrenceTargetChartGlue_isPullback (k : J i) (hk : dst i k = j) :
    IsPullback (principalOccurrenceOverlapProjection e x j)
      (principalOccurrenceOriginalOpenAt e i k hk)
      (principalOccurrenceTargetChartGlue e x hx i hc he)
      (principalOccurrenceAmbientProjection e x i) := by
  rw [principalOccurrenceTargetChartGlue_eq_open e x hx i hc he k hk]
  subst j
  exact principalOccurrenceOriginalOpen_isPullback e x hx i k

end FLT.Mazur.FiniteTypeRelationModel
