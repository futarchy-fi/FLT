/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOriginalCross

/-!
# Actual atlas comparison equations across distinct labels

Incidence squares in the original atlas force the two cross-chart routes
into any common ambient chart to agree. Consequently their actual finite
maps agree after projection from the original comparison domain.
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



/-- An original occurrence embedding with an explicitly identified overlap label. -/
def principalOccurrenceOriginalOpenAt {j : κ} (i : ι) (k : J i) (h : dst i k = j) :
    Spec (.of (Localization.Away (b j))) ⟶ Spec (.of (A i)) := by
  subst j
  exact principalOccurrenceOriginalOpen e i k

variable {X : Scheme.{u}} (U : ∀ i, Spec (.of (A i)) ⟶ X)
  (V : ∀ j, Spec (.of (Localization.Away (b j))) ⟶ X)
  (hUV : ∀ i k, principalOccurrenceOriginalOpen e i k ≫ U i = V (dst i k))

include hUV in
/-- Atlas incidence is unchanged by identifying the literal overlap label. -/
@[reassoc] theorem principalOccurrenceOriginalOpenAt_atlas {j : κ}
    (i : ι) (k : J i) (h : dst i k = j) :
    principalOccurrenceOriginalOpenAt e i k h ≫ U i = V j := by
  subst j
  exact hUV i k

include hUV in
/-- The two original patch arrows agree in the actual atlas. -/
@[reassoc] theorem principalOccurrenceOriginalPatch_atlas {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrenceOriginalPatchOther e p ≫ V (dst p.1.val.1 p.2) =
      principalOccurrenceOriginalPatchOpen e p ≫ V j := by
  obtain ⟨⟨⟨i, k⟩, rfl⟩, l⟩ := p
  rw [← hUV i l, ← hUV i k, ← Category.assoc, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ U i)
    (principalOccurrenceOriginalPatch_isPullback e i k l).w.symm

include hUV in
/-- Different outer labels give the same map from the common intersection into the atlas. -/
@[reassoc] theorem principalOccurrenceOriginalCross_atlas {j : κ}
    (p q : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrenceOriginalCrossOuterLeft e p q ≫ V (dst p.1.val.1 p.2) =
      principalOccurrenceOriginalCrossOuterRight e p q ≫ V (dst q.1.val.1 q.2) := by
  simp only [principalOccurrenceOriginalCrossOuterLeft, principalOccurrenceOriginalCrossOuterRight,
    Category.assoc, principalOccurrenceOriginalPatch_atlas e U V hUV]
  exact pullback.condition_assoc _

include hUV in
/-- Monicity of an atlas chart proves the actual original comparison equation. -/
theorem principalOccurrenceOriginalCross_comparison {j : κ}
    (p q : PrincipalOccurrencePatch (dst := dst) j) (i : ι) [Mono (U i)]
    (k l : J i) (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2) :
    principalOccurrenceOriginalCrossOuterLeft e p q ≫ principalOccurrenceOriginalOpenAt e i k hk =
      principalOccurrenceOriginalCrossOuterRight e p q ≫
        principalOccurrenceOriginalOpenAt e i l hl := by
  rw [← cancel_mono (U i)]
  simp only [Category.assoc, principalOccurrenceOriginalOpenAt_atlas e U V hUV]
  exact principalOccurrenceOriginalCross_atlas e U V hUV p q

variable [∀ i, Algebra.FiniteType R (A i)] [∀ j, Algebra.FiniteType R (B j)]
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))

/-- A finite occurrence embedding with an explicitly identified literal label. -/
def principalOccurrenceOpenAt {j : κ} (i : ι) (k : J i) (h : dst i k = j) :
    Spec (.of (PrincipalStage R (B j) (b j) (x.target j))) ⟶
      Spec (.of (Stage R (A i) (x.source i))) := by
  subst j
  exact principalOccurrenceOpen x hx i k

/-- The identified finite embedding recovers the original embedding on its entire scheme. -/
@[reassoc (attr := simp)] theorem principalOccurrenceOpenAt_recovery {j : κ}
    (i : ι) (k : J i) (h : dst i k = j) :
    principalOccurrenceOverlapProjection e x j ≫ principalOccurrenceOpenAt e x hx i k h =
      principalOccurrenceOriginalOpenAt e i k h ≫
        principalOccurrenceAmbientProjection e x i := by
  subst j
  exact principalOccurrenceOriginalOpen_fac e x hx i k

include hUV in
/-- Concrete finite atlas comparisons agree after projection from the original intersection. -/
theorem principalOccurrenceCross_comparison_recovery {j : κ}
    (p q : PrincipalOccurrencePatch (dst := dst) j) (i : ι) [Mono (U i)]
    (k l : J i) (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2) :
    principalOccurrenceOriginalCrossProjection e p q x hx ≫
        (principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk) =
      principalOccurrenceOriginalCrossProjection e p q x hx ≫
        (principalOccurrenceCrossOuterRight x hx p q ≫
          principalOccurrenceOpenAt e x hx i l hl) := by
  rw [principalOccurrenceOriginalCrossProjection_left_assoc,
    principalOccurrenceOriginalCrossProjection_right_assoc]
  simp only [principalOccurrenceOpenAt_recovery]
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ principalOccurrenceAmbientProjection e x i)
    (principalOccurrenceOriginalCross_comparison e U V hUV p q i k l hk hl)

end FLT.Mazur.FiniteTypeRelationModel
