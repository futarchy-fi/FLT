/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOriginalSubfamily
public import FLT.Mazur.PrincipalOccurrenceTargetChartGluing

/-!
# Recovery of glued target-chart morphisms

The finite patch cover pulls back to the original overlap. On that cover,
atlas incidence identifies every concrete route with the original target
map. Gluing therefore recovers the entire original morphism.
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

include hx in
/-- Every covering finite patch subfamily recovers a covering original patch subfamily. -/
theorem principalOccurrenceOriginalSubfamily_cover_of_stage {j : κ} {μ : Type*}
    (c : μ → PrincipalOccurrencePatch (dst := dst) j)
    (hc : (⨆ m, (principalOccurrencePatchOpen x hx (c m)).opensRange) = ⊤) :
    (⨆ m, (principalOccurrenceOriginalPatchOpen e (c m)).opensRange) = ⊤ := by
  apply top_unique
  intro z _
  have hz : principalOccurrenceOverlapProjection e x j z ∈
      ⨆ m, (principalOccurrencePatchOpen x hx (c m)).opensRange := by
    rw [hc]
    trivial
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨m, ?_⟩
  rw [← principalOccurrenceOriginalPatch_preimage e x hx]
  exact hm

variable {X : Scheme.{u}} (U : ∀ i, Spec (.of (A i)) ⟶ X)
  (V : ∀ j, Spec (.of (Localization.Away (b j))) ⟶ X)
  (hUV : ∀ i k, principalOccurrenceOriginalOpen e i k ≫ U i = V (dst i k))
  {j : κ} (i : ι) [Mono (U i)]
  (g : Spec (.of (Localization.Away (b j))) ⟶ Spec (.of (A i)))
  (hg : g ≫ U i = V j)

omit [∀ i, Algebra.FiniteType R (A i)] [∀ j, Algebra.FiniteType R (B j)] in
include hUV hg in
/-- Every original target-compatible patch route is the restriction of the original target map. -/
theorem principalOccurrenceOriginalTargetPatch_fac
    (p : PrincipalOccurrencePatchTo (dst := dst) j i) :
    principalOccurrenceOriginalPatchOther e p.1 ≫
        principalOccurrenceOriginalOpenAt e i p.2.val p.2.property =
      principalOccurrenceOriginalPatchOpen e p.1 ≫ g := by
  rw [← cancel_mono (U i), Category.assoc, Category.assoc, hg,
    principalOccurrenceOriginalOpenAt_atlas e U V hUV]
  exact principalOccurrenceOriginalPatch_atlas e U V hUV p.1

variable
  (hc : (⨆ p : PrincipalOccurrencePatchTo (dst := dst) j i,
    (principalOccurrencePatchOpen x hx p.1).opensRange) = ⊤)
  (he : ∀ p q : PrincipalOccurrencePatchTo (dst := dst) j i,
    principalOccurrenceCrossOuterLeft x hx p.1 q.1 ≫
        principalOccurrenceOpenAt e x hx i p.2.val p.2.property =
      principalOccurrenceCrossOuterRight x hx p.1 q.1 ≫
        principalOccurrenceOpenAt e x hx i q.2.val q.2.property)

attribute [local irreducible] principalOccurrenceTargetChartGlue

include hUV hg in
/-- The entire glued target-chart map recovers the original atlas morphism. -/
@[reassoc] theorem principalOccurrenceTargetChartGlue_recovery :
    principalOccurrenceOverlapProjection e x j ≫
        principalOccurrenceTargetChartGlue e x hx i hc he =
      g ≫ principalOccurrenceAmbientProjection e x i := by
  apply principalOccurrenceOriginalSubfamily_hom_ext e
    (fun p : PrincipalOccurrencePatchTo (dst := dst) j i ↦ p.1)
    (principalOccurrenceOriginalSubfamily_cover_of_stage e x hx _ hc)
  intro p
  rw [← principalOccurrenceOriginalPatchProjection_left_assoc e x hx p.1,
    principalOccurrenceTargetChartGlue_fac, principalOccurrenceTargetPatchMap,
    principalOccurrenceOriginalPatchProjection_right_assoc, principalOccurrenceOpenAt_recovery]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ principalOccurrenceAmbientProjection e x i)
    (principalOccurrenceOriginalTargetPatch_fac e U V hUV i g hg p)

end FLT.Mazur.FiniteTypeRelationModel
