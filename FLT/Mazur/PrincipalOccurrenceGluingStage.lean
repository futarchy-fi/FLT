/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonGluing
/-!
# The subtype of gluable occurrence stages

Membership records exactly the already constructed bijectivity and
ambient gluing geometry. Choosing witnesses gives the canonical glue data;
no transition compatibility is included in the predicate.
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

/-- The geometric conditions used by the established common-union gluing constructor. -/
def PrincipalOccurrenceGluingCondition
    (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom)) : Prop :=
  ∃ hx : ∀ i k, Function.Bijective (x.hom i k),
    ∃ he : (∀ j (p q : PrincipalOccurrencePatch (dst := dst) j)
    (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2),
    principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl),
      (∀ i, principalOccurrenceCommonUnion e x hx i i = ⊤) ∧
      (∀ i t r : ι,
    ∃ g : pullback (principalOccurrenceCommonUnion e x hx i t).ι
          (principalOccurrenceCommonUnion e x hx i r).ι ⟶
          (principalOccurrenceCommonUnion e x hx t r).toScheme,
      IsOpenImmersion g ∧
        g ≫ (principalOccurrenceCommonUnion e x hx t r).ι =
          pullback.fst _ _ ≫ (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
            (principalOccurrenceCommonUnion e x hx t i).ι ∧
        g ≫ (principalOccurrenceCommonUnionIso e x hx he t r).hom ≫
            (principalOccurrenceCommonUnion e x hx r t).ι =
          pullback.snd _ _ ≫ (principalOccurrenceCommonUnionIso e x hx he i r).hom ≫
            (principalOccurrenceCommonUnion e x hx r i).ι)

/-- The occurrence stages carrying the full gluing geometry, ordered by refinement. -/
abbrev PrincipalOccurrenceGluingStage :=
  {x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom) //
    PrincipalOccurrenceGluingCondition e x}

/-- Bijectivity supplied by membership in the geometric stage subtype. -/
abbrev principalOccurrenceGluingBijective (x : PrincipalOccurrenceGluingStage e) :=
  x.property.choose

/-- Exhaustive pair equations supplied by membership in the geometric stage subtype. -/
abbrev principalOccurrenceGluingEquations (x : PrincipalOccurrenceGluingStage e) :=
  x.property.choose_spec.choose

/-- The actual common-union glue data of a geometric stage. -/
def principalOccurrenceStageGlueData [Small.{u} ι] (x : PrincipalOccurrenceGluingStage e) :
    Scheme.GlueData.{u} :=
  principalOccurrenceCommonGlueData e x.val (principalOccurrenceGluingBijective e x)
    (principalOccurrenceGluingEquations e x) x.property.choose_spec.choose_spec.1
    x.property.choose_spec.choose_spec.2

end FLT.Mazur.FiniteTypeRelationModel
