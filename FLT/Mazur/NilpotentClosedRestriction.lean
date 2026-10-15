/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineEtaleNilpotentLift

/-!
# Nilpotent closed immersions on open neighborhoods

A nilpotent closed immersion has the same underlying topology as its target.
Its restriction and its pullback along any open immersion retain a nilpotent
kernel. These are scheme statements and do not identify their structure sheaves.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.NilpotentClosedRestriction
set_option backward.isDefEq.respectTransparency false
variable {T₀ T U : Scheme} (i : T₀ ⟶ T) [IsClosedImmersion i]
  (hi : IsNilpotent i.ker)

include hi in
/-- Nilpotent closed immersions cover every point of their target. -/
theorem surjective : Function.Surjective i := by
  have : IsDominant i := by
    obtain ⟨n, hn⟩ := hi
    rw [isDominant_iff, denseRange_iff_closure_range, ← i.support_ker,
      ← i.ker.support_pow (n + 1) (by simp), pow_succ, hn]
    simp
  exact i.surjective

/-- The underlying topology is unchanged, without discarding nilpotent sections. -/
def homeomorph : T₀ ≃ₜ T :=
  (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨i.isClosedEmbedding.isEmbedding, surjective i hi⟩).homeomorph

/-- Every open restriction retains the original nilpotence exponent. -/
theorem restrict_ker_pow {n : ℕ} (hn : i.ker ^ n = ⊥) (W : T.Opens) :
    (i ∣_ W).ker ^ n = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext V
  have h := congrArg (fun J : T.IdealSheafData ↦
    J.ideal ⟨W.ι ''ᵁ V, V.2.image_of_isOpenImmersion _⟩) hn
  simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Scheme.ker_morphismRestrict_ideal]
    using h

include hi in
/-- A restricted infinitesimal inclusion remains infinitesimal. -/
theorem restrict_nilpotent (W : T.Opens) : IsNilpotent (i ∣_ W).ker := by
  obtain ⟨n, hn⟩ := hi
  exact ⟨n, restrict_ker_pow i hn W⟩

include hi in
/-- Pullback to any open chart retains the nilpotent kernel, including on overlaps. -/
theorem pullback_nilpotent (j : U ⟶ T) [IsOpenImmersion j] :
    IsNilpotent (pullback.fst j i).ker := by
  obtain ⟨n, hn⟩ := hi
  refine ⟨n, le_antisymm ?_ bot_le⟩
  intro W
  change (pullback.fst j i).ker.ideal W ^ n ≤ ⊥
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion i _ _ j
    (IsPullback.of_hasPullback j i)]
  have h := congrArg (fun J : T.IdealSheafData ↦
    J.ideal ⟨j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩) hn
  change i.ker.ideal ⟨j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩ ^ n = ⊥ at h
  calc
    _ ≤ (i.ker.ideal ⟨j ''ᵁ W, W.2.image_of_isOpenImmersion _⟩ ^ n).comap
        (j.appIso W).inv.hom := Ideal.le_comap_pow (j.appIso W).inv.hom n
    _ = ⊥ := by
      rw [h, Ideal.comap_bot_of_injective _ (ConcreteCategory.bijective_of_isIso _).1]

end FLT.Mazur.NilpotentClosedRestriction
