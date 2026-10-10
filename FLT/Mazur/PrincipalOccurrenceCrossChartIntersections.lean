/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOverlapPatches

/-!
# Cross-chart intersections of occurrence patches

Double opens from different ambient charts meet inside their one literal
shared overlap. Their pullback gives an actual common comparison domain,
with open immersions to both double opens and both outer overlap labels.
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
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}
  (x : PrincipalOccurrenceStage dst a b f) (hx : ∀ i e, Function.Bijective (x.hom i e))


variable {j : κ} (p q : PrincipalOccurrencePatch (dst := dst) j)

/-- Intersect patches whose ambient charts and second overlap labels may differ. -/
abbrev principalOccurrenceCross : Scheme.{u} :=
  pullback (principalOccurrencePatchOpen x hx p) (principalOccurrencePatchOpen x hx q)

/-- The first double-open projection of a cross-chart intersection. -/
abbrev principalOccurrenceCrossLeft :
    principalOccurrenceCross x hx p q ⟶ principalOccurrencePatchScheme x p :=
  pullback.fst _ _

/-- The second double-open projection of a cross-chart intersection. -/
abbrev principalOccurrenceCrossRight :
    principalOccurrenceCross x hx p q ⟶ principalOccurrencePatchScheme x q :=
  pullback.snd _ _

/-- The cross-chart intersection is an open subscheme of the shared overlap. -/
def principalOccurrenceCrossOpen : principalOccurrenceCross x hx p q ⟶
    Spec (.of (PrincipalStage R (B j) (b j) (x.target j))) :=
  principalOccurrenceCrossLeft x hx p q ≫ principalOccurrencePatchOpen x hx p

/-- Both ambient-chart presentations give the same shared-overlap map. -/
@[reassoc (attr := simp)] theorem principalOccurrenceCross_right_fac :
    principalOccurrenceCrossRight x hx p q ≫ principalOccurrencePatchOpen x hx q =
      principalOccurrenceCrossOpen x hx p q :=
  pullback.condition.symm

/-- Either outer overlap contains the common comparison domain as an open subscheme. -/
instance principalOccurrenceCrossOpen_isOpenImmersion :
    IsOpenImmersion (principalOccurrenceCrossOpen x hx p q) := by
  dsimp only [principalOccurrenceCrossOpen, principalOccurrenceCrossLeft]
  infer_instance

/-- The cross-chart domain is exactly the intersection of the two patch images. -/
theorem principalOccurrenceCross_opensRange :
    (principalOccurrenceCrossOpen x hx p q).opensRange =
      (principalOccurrencePatchOpen x hx p).opensRange ⊓
        (principalOccurrencePatchOpen x hx q).opensRange := by
  dsimp only [principalOccurrenceCrossOpen, principalOccurrenceCrossLeft]
  rw [Scheme.Hom.opensRange_comp, Scheme.Hom.opensRange_pullbackFst,
    Scheme.Hom.image_preimage_eq_opensRange_inf]

/-- Restrict to the first outer overlap, which need not have the shared label. -/
def principalOccurrenceCrossOuterLeft : principalOccurrenceCross x hx p q ⟶
    Spec (.of (PrincipalStage R (B (dst p.1.val.1 p.2)) (b (dst p.1.val.1 p.2))
      (x.target (dst p.1.val.1 p.2)))) :=
  principalOccurrenceCrossLeft x hx p q ≫ principalOccurrencePatchOther x hx p

/-- Restrict to the second outer overlap in the other ambient chart. -/
def principalOccurrenceCrossOuterRight : principalOccurrenceCross x hx p q ⟶
    Spec (.of (PrincipalStage R (B (dst q.1.val.1 q.2)) (b (dst q.1.val.1 q.2))
      (x.target (dst q.1.val.1 q.2)))) :=
  principalOccurrenceCrossRight x hx p q ≫ principalOccurrencePatchOther x hx q

/-- The first outer restriction is an open immersion. -/
instance principalOccurrenceCrossOuterLeft_isOpenImmersion :
    IsOpenImmersion (principalOccurrenceCrossOuterLeft x hx p q) := by
  dsimp only [principalOccurrenceCrossOuterLeft, principalOccurrenceCrossLeft]
  infer_instance

/-- The second outer restriction is an open immersion. -/
instance principalOccurrenceCrossOuterRight_isOpenImmersion :
    IsOpenImmersion (principalOccurrenceCrossOuterRight x hx p q) := by
  dsimp only [principalOccurrenceCrossOuterRight, principalOccurrenceCrossRight]
  infer_instance

end FLT.Mazur.FiniteTypeRelationModel
