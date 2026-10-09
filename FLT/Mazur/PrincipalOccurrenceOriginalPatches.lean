/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOriginalGeometry
public import FLT.Mazur.PrincipalOccurrenceOverlapPatches

/-!
# Original double-open patches and their recovery maps

The original atlas supplies both arrows of every double-open patch. The
cartesian finite intersection constructs its projection and proves recovery
of both overlap labels, even when those labels differ.
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


/-- Restrict an original principal open into an incident original overlap. -/
def principalOccurrenceOriginalRestriction (i : ι) (k : J i) {r : A i}
    (h : PrimeSpectrum.basicOpen r ≤ PrimeSpectrum.basicOpen (a i k)) :
    Spec (.of (Localization.Away r)) ⟶ Spec (.of (Localization.Away (b (dst i k)))) :=
  PrincipalLocalizationSquare.openInclusion h ≫
    (Scheme.Spec.mapIso ((e i k).toRingEquiv.toCommRingCatIso.op)).inv

/-- Original restrictions retain their ambient embedding. -/
@[reassoc (attr := simp)] theorem principalOccurrenceOriginalRestriction_fac
    (i : ι) (k : J i) {r : A i}
    (h : PrimeSpectrum.basicOpen r ≤ PrimeSpectrum.basicOpen (a i k)) :
    principalOccurrenceOriginalRestriction e i k h ≫ principalOccurrenceOriginalOpen e i k =
      PrincipalLocalizationSquare.inclusion r := by
  dsimp only [principalOccurrenceOriginalRestriction, principalOccurrenceOriginalOpen]
  rw [Category.assoc, Iso.inv_hom_id_assoc, PrincipalLocalizationSquare.openInclusion_fac]

/-- The actual original double principal open in the patch's ambient chart. -/
abbrev principalOccurrenceOriginalPatch {j : κ} (p : PrincipalOccurrencePatch (dst := dst) j) :
    Scheme.{u} :=
  Spec (.of (Localization.Away (a p.1.val.1 p.1.val.2 * a p.1.val.1 p.2)))

/-- The original patch maps into its literal shared overlap. -/
def principalOccurrenceOriginalPatchOpen {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrenceOriginalPatch (a := a) p ⟶ Spec (.of (Localization.Away (b j))) := by
  obtain ⟨⟨⟨i, k⟩, rfl⟩, l⟩ := p
  exact principalOccurrenceOriginalRestriction e i k (PrimeSpectrum.basicOpen_mul_le_left _ _)

/-- The original patch also maps into the other overlap label. -/
def principalOccurrenceOriginalPatchOther {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrenceOriginalPatch (a := a) p ⟶
      Spec (.of (Localization.Away (b (dst p.1.val.1 p.2)))) :=
  principalOccurrenceOriginalRestriction e p.1.val.1 p.2
    (PrimeSpectrum.basicOpen_mul_le_right _ _)

/-- The original patch is the genuine intersection of its two overlap labels. -/
theorem principalOccurrenceOriginalPatch_isPullback (i : ι) (k l : J i) :
    IsPullback
      (principalOccurrenceOriginalPatchOpen e ⟨⟨⟨i, k⟩, rfl⟩, l⟩)
      (principalOccurrenceOriginalPatchOther e ⟨⟨⟨i, k⟩, rfl⟩, l⟩)
      (principalOccurrenceOriginalOpen e i k) (principalOccurrenceOriginalOpen e i l) :=
  principalProduct_isPullback_of_isos _ _
    (Scheme.Spec.mapIso ((e i k).toRingEquiv.toCommRingCatIso.op))
    (Scheme.Spec.mapIso ((e i l).toRingEquiv.toCommRingCatIso.op))

variable [∀ i, Algebra.FiniteType R (A i)] [∀ j, Algebra.FiniteType R (B j)]
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))

/-- Project an original patch into the actual finite double open. -/
def principalOccurrenceOriginalPatchProjection {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrenceOriginalPatch (a := a) p ⟶ principalOccurrencePatchScheme x p := by
  obtain ⟨⟨⟨i, k⟩, rfl⟩, l⟩ := p
  apply (principalOccurrencePatch_isPullback x hx i k l).lift
    (principalOccurrenceOriginalPatchOpen e ⟨⟨⟨i, k⟩, rfl⟩, l⟩ ≫
      principalOccurrenceOverlapProjection e x (dst i k))
    (principalOccurrenceOriginalPatchOther e ⟨⟨⟨i, k⟩, rfl⟩, l⟩ ≫
      principalOccurrenceOverlapProjection e x (dst i l))
  rw [Category.assoc, Category.assoc, principalOccurrenceOriginalOpen_fac,
    principalOccurrenceOriginalOpen_fac, ← Category.assoc, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ principalOccurrenceAmbientProjection e x i)
    (principalOccurrenceOriginalPatch_isPullback e i k l).w

/-- Projection recovers the map into the shared original overlap. -/
@[reassoc (attr := simp)] theorem principalOccurrenceOriginalPatchProjection_left {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrenceOriginalPatchProjection e x hx p ≫ principalOccurrencePatchOpen x hx p =
      principalOccurrenceOriginalPatchOpen e p ≫ principalOccurrenceOverlapProjection e x j := by
  obtain ⟨⟨⟨i, k⟩, rfl⟩, l⟩ := p
  exact (principalOccurrencePatch_isPullback x hx i k l).lift_fst _ _ _

/-- Projection also recovers the other label, not just the chosen shared label. -/
@[reassoc (attr := simp)] theorem principalOccurrenceOriginalPatchProjection_right {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrenceOriginalPatchProjection e x hx p ≫ principalOccurrencePatchOther x hx p =
      principalOccurrenceOriginalPatchOther e p ≫
        principalOccurrenceOverlapProjection e x (dst p.1.val.1 p.2) := by
  obtain ⟨⟨⟨i, k⟩, rfl⟩, l⟩ := p
  exact (principalOccurrencePatch_isPullback x hx i k l).lift_snd _ _ _

end FLT.Mazur.FiniteTypeRelationModel
