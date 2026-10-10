/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonUnion
public import FLT.Mazur.FiniteRelationSpectrum

/-!
# Common occurrence gluing retains the affine base

Every literal overlap embedding comes from an algebra homomorphism over
the original ring. The common-union comparison therefore identifies the
two actual structure maps to that same affine base.
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

/-- Structure map of an actual finite ambient chart to the original affine base. -/
abbrev principalOccurrenceChartStructure (i : ι) :
    Spec (.of (Stage R (A i) (x.source i))) ⟶ Spec (.of R) :=
  FiniteRelationModel.stageStructure R (relationIdeal R (A i)) (x.source i)

/-- Each literal overlap embedding commutes with the structure maps over the same ring. -/
@[reassoc] theorem principalOccurrenceOpenAt_over {j : κ} (i : ι) (k : J i)
    (h : dst i k = j) :
    principalOccurrenceOpenAt e x hx i k h ≫ principalOccurrenceChartStructure e x i =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (PrincipalStage R (B j) (b j) (x.target j)))) := by
  subst j
  change principalOccurrenceOpen x hx i k ≫ _ = _
  rw [principalOccurrenceOpen_eq_spec]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (principalOccurrenceAmbientHom x i k).comp_algebraMap

variable
  (he : ∀ j (p q : PrincipalOccurrencePatch (dst := dst) j)
    (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2),
    principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl)

/-- Common-union comparisons preserve the original affine base, on the full union. -/
@[reassoc] theorem principalOccurrenceCommonUnionIso_over (i t : ι) :
    (principalOccurrenceCommonUnion e x hx i t).ι ≫ principalOccurrenceChartStructure e x i =
      (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
        (principalOccurrenceCommonUnion e x hx t i).ι ≫
          principalOccurrenceChartStructure e x t := by
  apply openImageUnion_hom_ext (principalOccurrenceCommonLeft e x hx i t)
  intro p
  have hl := congrArg (fun k ↦ k ≫ principalOccurrenceChartStructure e x i)
    (openImageUnionMap_fac (principalOccurrenceCommonLeft e x hx i t) p)
  have hr := congrArg (fun k ↦ k ≫ principalOccurrenceChartStructure e x t)
    (openImageUnionMap_fac (principalOccurrenceCommonLeft e x hx t i)
      (principalOccurrenceCommonSwap dst i t p))
  have hi := congrArg (fun k ↦ k ≫ (principalOccurrenceCommonUnion e x hx t i).ι ≫
      principalOccurrenceChartStructure e x t)
    (principalOccurrenceCommonUnionIso_fac e x hx he i t p)
  exact (Category.assoc _ _ _).symm.trans (hl.trans
    ((principalOccurrenceOpenAt_over e x hx i p.2.1.val p.2.1.property).trans
      ((principalOccurrenceOpenAt_over e x hx t p.2.2.val p.2.2.property).symm.trans
        (hr.symm.trans ((Category.assoc _ _ _).trans
          (hi.symm.trans (Category.assoc _ _ _)))))))

end FLT.Mazur.FiniteTypeRelationModel
