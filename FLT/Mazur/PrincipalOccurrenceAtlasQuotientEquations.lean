/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCrossQuotientCoordinates
public import FLT.Mazur.PrincipalOccurrenceAtlasComparisons

/-!
# Concrete atlas comparison equations in the canonical quotient rings

The comparison maps are extracted from the actual finite scheme routes.
Atlas incidence and monicity of its ambient charts prove their equality in
the exact quotient rings used by local equation descent.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

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


variable {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)



/-- The left concrete ambient comparison in the actual finite cross-chart coordinate ring. -/
def principalOccurrenceCrossComparisonLeft (i : ι) (k : J i)
    (hk : dst i k = dst p.1.val.1 p.2) :
    Stage R (A i) (x.source i) →+* PrincipalOccurrenceCrossRing x p q :=
  (Spec.preimage ((principalOccurrenceCrossIso x hx p q).inv ≫
    principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk)).hom

/-- The right comparison may pass through a different ambient chart and a different outer label. -/
def principalOccurrenceCrossComparisonRight (i : ι) (l : J i)
    (hl : dst i l = dst q.1.val.1 q.2) :
    Stage R (A i) (x.source i) →+* PrincipalOccurrenceCrossRing x p q :=
  (Spec.preimage ((principalOccurrenceCrossIso x hx p q).inv ≫
    principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl)).hom

variable {X : Scheme.{u}} (U : ∀ i, Spec (.of (A i)) ⟶ X)
  (V : ∀ j, Spec (.of (Localization.Away (b j))) ⟶ X)
  (hUV : ∀ i k, principalOccurrenceOriginalOpen e i k ≫ U i = V (dst i k))

include hUV in
/-- Canonical quotient coordinates satisfy the actual finite atlas comparison equation. -/
theorem principalOccurrenceCrossQuotient_comparison (i : ι) [Mono (U i)]
    (k l : J i) (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2) :
    principalOccurrenceCrossQuotientFinite e x hx p q ≫
        (principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk) =
      principalOccurrenceCrossQuotientFinite e x hx p q ≫
        (principalOccurrenceCrossOuterRight x hx p q ≫
          principalOccurrenceOpenAt e x hx i l hl) := by
  rw [← principalOccurrenceCrossQuotientOriginal_fac e x hx p q]
  simp only [Category.assoc]
  exact congrArg (fun f ↦ principalOccurrenceCrossQuotientOriginal e x hx p q ≫ f)
    (principalOccurrenceCross_comparison_recovery e U V hUV x hx p q i k l hk hl)

include hUV in
/-- The full concrete coordinate maps agree after the canonical quotient projection. -/
theorem principalOccurrenceCrossComparison_quotient (i : ι) [Mono (U i)]
    (k l : J i) (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2) :
    (principalOccurrenceCrossToQuotient e x p q).toRingHom.comp
        (principalOccurrenceCrossComparisonLeft e x hx p q i k hk) =
      (principalOccurrenceCrossToQuotient e x p q).toRingHom.comp
        (principalOccurrenceCrossComparisonRight e x hx p q i l hl) := by
  apply_fun fun f ↦ Spec.map (CommRingCat.ofHom f) using
    fun _ _ h ↦ congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  change Spec.map (Spec.preimage _ ≫
      CommRingCat.ofHom (principalOccurrenceCrossToQuotient e x p q).toRingHom) =
    Spec.map (Spec.preimage _ ≫
      CommRingCat.ofHom (principalOccurrenceCrossToQuotient e x p q).toRingHom)
  rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
  simpa only [principalOccurrenceCrossQuotientFinite, Category.assoc] using
    principalOccurrenceCrossQuotient_comparison e x hx p q U V hUV i k l hk hl

end FLT.Mazur.FiniteTypeRelationModel
