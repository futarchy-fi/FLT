/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeExactRankFinite
public import FLT.Mazur.SchemeEffectiveEpiSections
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Faithful coefficient descent on positive exact-rank schemes

The whole original source is itself a finite etale surjection over a positive
exact-rank coefficient scheme. Its section map detects every ideal-power
zero equation and descends compatible coefficients uniquely, including nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] [LocallyQuasiFinite E.hom]
  (n : ℕ) (o : Fin n) {B : Scheme} (b : B ⟶ S)
  (hb : Set.range b ⊆ exactRank E n)
local notation "π" => pullback.snd E.hom b
include o hb

omit [QuasiCompact E.hom] [LocallyQuasiFinite E.hom] in
/-- The full original source covers every coefficient point of positive exact rank. -/
theorem exactRank_source_surjective : Function.Surjective π := by
  intro x
  have hx : x ∈ Set.range π := by
    rw [Scheme.Pullback.range_snd]
    obtain ⟨t, ht⟩ := (hb (Set.mem_range_self x)).1
    refine ⟨(distinctCoordinate E (Fin n) o).left t, ?_⟩
    exact (congrArg (fun f ↦ f t) (distinctCoordinate E (Fin n) o).w).trans ht
  exact hx

/-- The finite full-source cover is an effective epimorphism of the actual coefficient scheme. -/
theorem exactRank_source_effectiveEpi : EffectiveEpi π := by
  let _ := finite_pullback_of_exactRank E n b hb
  let _ : Surjective π := ⟨exactRank_source_surjective E n o b hb⟩
  infer_instance

/-- Equality of original coefficients is faithfully detected on the unsplit finite source. -/
theorem exactRank_source_appTop_injective : Function.Injective (π).appTop := by
  let _ := exactRank_source_effectiveEpi E n o b hb
  exact SchemeEffectiveEpiSections.appTop_injective π

/-- No original nilpotent is discarded: each fixed ideal-power zero equation is detected. -/
theorem exactRank_source_ideal_pow_eq_bot_iff (J : Ideal Γ(B, ⊤)) (k : ℕ) :
    (J.map (π).appTop.hom) ^ k = ⊥ ↔ J ^ k = ⊥ := by
  rw [← Ideal.map_pow]
  exact Ideal.map_eq_bot_iff_of_injective (exactRank_source_appTop_injective E n o b hb)

/-- Affine stage coefficients embed faithfully flatly into their finite full-source algebra. -/
theorem exactRank_source_faithfullyFlat [IsAffine B] : (π).appTop.hom.FaithfullyFlat := by
  let _ := finite_pullback_of_exactRank E n b hb
  let _ : IsAffine (pullback E.hom b) := isAffine_of_isAffineHom π
  let _ : Surjective π := ⟨exactRank_source_surjective E n o b hb⟩
  exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine π).mp
    ⟨inferInstance, inferInstance⟩

/-- Every compatible coefficient on the full original source descends uniquely to its stage. -/
theorem exactRank_source_sections_existsUnique (t : Γ(pullback E.hom b, ⊤))
    (ht : (pullback.fst π π).appTop t = (pullback.snd π π).appTop t) :
    ∃! u : Γ(B, ⊤), (π).appTop u = t := by
  let _ := exactRank_source_effectiveEpi E n o b hb
  exact SchemeEffectiveEpiSections.sections_existsUnique (IsPullback.of_hasPullback π π) t ht

end FLT.Mazur.RelativeOrderedTuples
