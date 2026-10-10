/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrencePatchImageIsomorphisms
public import FLT.Mazur.PrincipalOccurrenceAtlasComparisons

/-!
# Image identifications retain both overlap routes

Actual cross-chart comparison equations identify the target routes along a
patch image isomorphism. For a common outer label, cancellation of its open
embedding proves compatibility with the second overlap arrow itself.
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
  {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)
  (h : (principalOccurrencePatchOpen x hx p).opensRange =
    (principalOccurrencePatchOpen x hx q).opensRange)

/-- Cross-chart equality identifies the target routes along the actual image isomorphism. -/
theorem principalOccurrencePatchImageIso_route (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2)
    (he : principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl) :
    (principalOccurrencePatchImageIso x hx p q h).hom ≫
        principalOccurrencePatchOther x hx q ≫ principalOccurrenceOpenAt e x hx i l hl =
      principalOccurrencePatchOther x hx p ≫ principalOccurrenceOpenAt e x hx i k hk := by
  let d : principalOccurrencePatchScheme x p ⟶ principalOccurrenceCross x hx p q :=
    pullback.lift (𝟙 _) (principalOccurrencePatchImageIso x hx p q h).hom
      (by rw [Category.id_comp, principalOccurrencePatchImageIso_fac])
  have hd := congrArg (fun k ↦ d ≫ k) he
  dsimp only [principalOccurrenceCrossOuterLeft, principalOccurrenceCrossOuterRight,
    principalOccurrenceCrossLeft, principalOccurrenceCrossRight] at hd
  simpa only [Category.assoc, d, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
    Category.id_comp] using hd.symm

/-- Identify the outer overlap label without changing the geometric arrow. -/
def principalOccurrencePatchOtherAt {r : κ}
    (hp : dst p.1.val.1 p.2 = r) :
    principalOccurrencePatchScheme x p ⟶
      Spec (.of (PrincipalStage R (B r) (b r) (x.target r))) := by
  subst r
  exact principalOccurrencePatchOther x hx p

/-- The transported outer arrow has its original route into every incident chart. -/
@[reassoc] theorem principalOccurrencePatchOtherAt_fac {r : κ}
    (hp : dst p.1.val.1 p.2 = r) (i : ι) (k : J i) (hk : dst i k = r) :
    principalOccurrencePatchOtherAt e x hx p hp ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrencePatchOther x hx p ≫
        principalOccurrenceOpenAt e x hx i k (hk.trans hp.symm) := by
  subst r
  rfl

/-- The image isomorphism preserves the second overlap arrow, with explicit common labels. -/
@[reassoc] theorem principalOccurrencePatchImageIso_other (i : ι) (k : J i)
    (hp : dst p.1.val.1 p.2 = dst i k) (hq : dst q.1.val.1 q.2 = dst i k)
    (he : principalOccurrenceCrossOuterLeft x hx p q ≫
        principalOccurrenceOpenAt e x hx i k hp.symm =
      principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i k hq.symm) :
    (principalOccurrencePatchImageIso x hx p q h).hom ≫
        principalOccurrencePatchOtherAt e x hx q hq =
      principalOccurrencePatchOtherAt e x hx p hp := by
  apply (cancel_mono (principalOccurrenceOpen x hx i k)).mp
  rw [Category.assoc]
  change (principalOccurrencePatchImageIso x hx p q h).hom ≫
      principalOccurrencePatchOtherAt e x hx q hq ≫ principalOccurrenceOpenAt e x hx i k rfl =
    principalOccurrencePatchOtherAt e x hx p hp ≫ principalOccurrenceOpenAt e x hx i k rfl
  rw [principalOccurrencePatchOtherAt_fac e x hx q hq i k rfl,
    principalOccurrencePatchOtherAt_fac e x hx p hp i k rfl]
  exact principalOccurrencePatchImageIso_route e x hx p q h i k k hp.symm hq.symm he

end FLT.Mazur.FiniteTypeRelationModel
