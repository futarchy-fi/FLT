/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFlatTargetOpen

/-!
# Detecting whole-source flat neighborhoods by open parametrizations

An open immersion with flat complete source pullback contributes its entire
image to the maximal flat target open. The statement also applies to a
Cartesian presentation, without choosing a reduced source or target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFlatTargetOpen
set_option backward.isDefEq.respectTransparency false
variable {X Y Z P : Scheme.{u}} (f : X ⟶ Y) (j : Z ⟶ Y) [IsOpenImmersion j]

/-- An actual flat Cartesian neighborhood lies in the maximal whole-source flat open. -/
theorem opensRange_le_of_isPullback (a : P ⟶ X) (p : P ⟶ Z)
    (h : IsPullback a p f j) [Flat p] : j.opensRange ≤ locus f := by
  let e := j.isoOpensRange
  have he : e.inv ≫ j = j.opensRange.ι :=
    Scheme.Hom.isoOpensRange_inv_comp j
  have h₁ := IsPullback.of_horiz_isIso
    (show CommSq (𝟙 P) (p ≫ e.hom) p e.inv from ⟨by simp⟩)
  have h₂ := h₁.paste_horiz h
  simp only [Category.id_comp, he] at h₂
  apply (le_locus_iff f _).mpr
  rw [← h₂.isoPullback_inv_snd]
  infer_instance

/-- In particular every open base change with flat complete source is retained. -/
theorem opensRange_le [Flat (pullback.snd f j)] : j.opensRange ≤ locus f :=
  opensRange_le_of_isPullback f j _ _ (IsPullback.of_hasPullback f j)

/-- Flatness on an open base change is equivalent to inclusion of its target image. -/
theorem opensRange_le_iff : j.opensRange ≤ locus f ↔ Flat (pullback.snd f j) := by
  refine ⟨fun hj ↦ ?_, fun _ ↦ opensRange_le f j⟩
  let _ := flat_of_le f j.opensRange hj
  have he : j.isoOpensRange.hom ≫ j.opensRange.ι = j :=
    Scheme.Hom.isoOpensRange_hom_ι j
  let h := (IsPullback.of_hasPullback (pullback.snd f j.opensRange.ι)
    j.isoOpensRange.hom).paste_horiz (IsPullback.of_hasPullback f j.opensRange.ι)
  rw [he] at h
  rw [← h.isoPullback_inv_snd]
  infer_instance

end FLT.Mazur.SchemeFlatTargetOpen
