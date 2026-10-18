/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicQuotient
public import FLT.Mazur.CyclicCharacteristicMarkedRelation

/-!
# The characteristic quotient coequalizes the actual marked relation

Compose the original normalization with its constructed finite-group quotient.
The resulting map is universal for original-locus maps that coequalize the
represented marked relation and are invariant under the actual relabelings.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- The actual original subgroup parameter maps into its characteristic quotient. -/
def locusToQuotient : locus n b ⟶ normalizedQuotient n b :=
  normalization n b ≫ normalizedQuotientMap n b

/-- The quotient map coequalizes the actual represented marked-comparison relation. -/
@[reassoc] theorem markedRelation_quotient :
    markedRelationFirst n b ≫ locusToQuotient n b =
      markedRelationSecond n b ≫ locusToQuotient n b := by
  unfold locusToQuotient
  rw [markedRelation_condition_assoc]

/-- Relabeling the original subgroup parameter preserves its actual quotient map. -/
@[reassoc] theorem locusToQuotient_invariant (g : RelabelGroup n) :
    (relabelAction n b g).hom ≫ locusToQuotient n b = locusToQuotient n b := by
  unfold locusToQuotient
  rw [← normalization_equivariant_assoc, normalizedQuotientMap_invariant]

variable {Y : Scheme} (f : locus n b ⟶ Y)
  (hr : markedRelationFirst n b ≫ f = markedRelationSecond n b ≫ f)

include hr in
/-- Coequalizing the original marked relation gives the actual normalization factorization. -/
theorem markedRelation_factor : normalization n b ≫ normalizedInclusion n b ≫ f = f := by
  let p : locus n b ⟶ markedRelation n b :=
    pullback.lift (𝟙 _) (normalization n b ≫ normalizedInclusion n b) (by
      rw [Category.id_comp, Category.assoc, normalizedInclusion_normalization, Category.comp_id])
  have hp := congrArg (fun k => p ≫ k) hr
  change p ≫ pullback.fst _ _ ≫ f = p ≫ pullback.snd _ _ ≫ f at hp
  simpa only [p, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
    Category.id_comp, Category.assoc] using hp.symm

variable (hf : ∀ g : RelabelGroup n, (relabelAction n b g).hom ≫ f = f)

include hr hf in
/-- The actual normalized factor inherits invariance from the original relation-invariant map. -/
theorem markedRelation_factor_invariant (g : RelabelGroup n) :
    (normalizedRelabelAction n b g).hom ≫ normalizedInclusion n b ≫ f =
      normalizedInclusion n b ≫ f := by
  have he : normalization n b ≫ (normalizedRelabelAction n b g).hom ≫
      normalizedInclusion n b ≫ f = f := by
    rw [normalization_equivariant_assoc, markedRelation_factor n b f hr, hf]
  have hh := congrArg (fun k => normalizedInclusion n b ≫ k) he
  simpa only [normalizedInclusion_normalization_assoc] using hh

include hr hf in
/-- The actual characteristic quotient is universal for marked comparisons and relabelings. -/
theorem locusToQuotient_existsUnique_desc :
    ∃! k : normalizedQuotient n b ⟶ Y, locusToQuotient n b ≫ k = f := by
  obtain ⟨k, hk, hu⟩ := normalizedQuotientMap_existsUnique_desc n b
    (normalizedInclusion n b ≫ f) (markedRelation_factor_invariant n b f hr hf)
  refine ⟨k, ?_, ?_⟩
  · change (normalization n b ≫ normalizedQuotientMap n b) ≫ k = f
    rw [Category.assoc, hk, markedRelation_factor n b f hr]
  · intro l hl
    apply hu
    have hh := congrArg (fun k => normalizedInclusion n b ≫ k) hl
    change normalizedInclusion n b ≫ (normalization n b ≫ normalizedQuotientMap n b) ≫ l =
      normalizedInclusion n b ≫ f at hh
    simpa only [Category.assoc, normalizedInclusion_normalization_assoc] using hh

/-- Unique factorization through the actual quotient is exactly the two original invariances. -/
theorem locusToQuotient_invariant_iff_existsUnique_desc :
    (markedRelationFirst n b ≫ f = markedRelationSecond n b ≫ f) ∧
      (∀ g : RelabelGroup n, (relabelAction n b g).hom ≫ f = f) ↔
        ∃! k : normalizedQuotient n b ⟶ Y, locusToQuotient n b ≫ k = f := by
  constructor
  · rintro ⟨hr, hf⟩
    exact locusToQuotient_existsUnique_desc n b f hr hf
  · rintro ⟨k, hk, _⟩
    rw [← hk]
    exact ⟨markedRelation_quotient_assoc n b k, fun g => locusToQuotient_invariant_assoc n b g k⟩

end FLT.Mazur.CyclicCharacteristicAtlas
