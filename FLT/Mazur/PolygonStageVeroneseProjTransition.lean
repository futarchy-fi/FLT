/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageVeroneseProj
public import FLT.Mazur.PolygonStageVeroneseTransition

/-!
# Original restriction maps between retained stage projective spectra

Homogeneous lifting makes each original stage restriction induce a global
Proj morphism. These morphisms retain evaluation into the compatible Proj
and the prescribed homogeneous-localization maps on every standard chart.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Proj.map

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Positive degrees lift through the original retained stage restriction. -/
theorem boundaryVeroneseTransition_irrelevant {a b : ℕ} (f : a ⟶ b) :
    (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) a)₊ ≤
      (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) b)₊.map
        (boundaryVeroneseTransition K n h (exactVeroneseStep K n h) f) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (toIdeal_irrelevant_le _).mpr
  intro d hd s hs
  obtain ⟨t, ht⟩ := boundaryVeroneseTransition_homogeneous_surjective K n h f d ⟨s, hs⟩
  change boundaryVeroneseTransition K n h (exactVeroneseStep K n h) f t = s at ht
  rw [← ht]
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ hd t.property)

/-- The original stage restriction induces the corresponding geometric stage map. -/
def boundaryVeroneseProjTransition {a b : ℕ} (f : a ⟶ b) :
    boundaryExactVeroneseProj K n h a ⟶ boundaryExactVeroneseProj K n h b :=
  Proj.map (boundaryVeroneseTransition K n h (exactVeroneseStep K n h) f)
    (boundaryVeroneseTransition_irrelevant K n h f)

/-- The original stage Proj maps commute with the original evaluations into the candidate. -/
@[reassoc]
theorem boundaryVeroneseProjTransition_toCompatible {a b : ℕ} (f : a ⟶ b) :
    boundaryVeroneseProjTransition K n h f ≫ boundaryVeroneseProjToCompatible K n h b =
      boundaryVeroneseProjToCompatible K n h a := by
  unfold boundaryVeroneseProjTransition boundaryVeroneseProjToCompatible
  simp only [← Proj.map_comp, boundaryVeroneseTransition_evaluation]

/-- Each standard chart map is localization of the specified original stage restriction. -/
@[reassoc]
theorem boundaryVeroneseProjTransition_away {a b : ℕ} (f : a ⟶ b) (d : ℕ) (hd : 0 < d)
    (s : boundaryVeroneseRing K n h (exactVeroneseStep K n h) b)
    (hs : s ∈ boundaryVeroneseGrade K n h (exactVeroneseStep K n h) b d) :
    Proj.awayι (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) a)
        (boundaryVeroneseTransition K n h (exactVeroneseStep K n h) f s)
        ((boundaryVeroneseTransition K n h _ f).map_mem hs) hd ≫
      boundaryVeroneseProjTransition K n h f =
        Spec.map (CommRingCat.ofHom
          (Away.map (boundaryVeroneseTransition K n h (exactVeroneseStep K n h) f) s)) ≫
            Proj.awayι (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) b) s hs hd :=
  Proj.awayι_comp_map (boundaryVeroneseTransition K n h _ f)
    (boundaryVeroneseTransition_irrelevant K n h f) hd s hs

end FLT.Mazur.PolygonInfinitesimalStages
