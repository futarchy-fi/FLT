/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageProj
public import FLT.Mazur.PolygonArithmeticStageTransition

/-!
# Original restriction maps between retained stage projective spectra

Homogeneous lifting makes each original stage restriction induce a global
Proj morphism. These morphisms retain evaluation into the compatible Proj
and the prescribed homogeneous-localization maps on every standard chart.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] Proj.map

variable (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (π : A) (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π) (n : ℕ) (h : 2 ≤ n)
    [NeZero n]

/-- Positive degrees lift through the original retained stage restriction. -/
theorem boundaryVeroneseTransition_irrelevant {a b : ℕ} (f : a ⟶ b) :
    (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) a)₊ ≤
      (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) b)₊.map
        (boundaryVeroneseTransition A π n h (exactVeroneseStep A π hne hgen n h) f) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (toIdeal_irrelevant_le _).mpr
  intro d hd s hs
  obtain ⟨t, ht⟩ := boundaryVeroneseTransition_homogeneous_surjective A π n h hne hgen f d ⟨s, hs⟩
  change boundaryVeroneseTransition A π n h (exactVeroneseStep A π hne hgen n h) f t = s at ht
  rw [← ht]
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ hd t.property)

/-- The original stage restriction induces the corresponding geometric stage map. -/
def boundaryVeroneseProjTransition {a b : ℕ} (f : a ⟶ b) :
    boundaryExactVeroneseProj A π n h hne hgen a ⟶ boundaryExactVeroneseProj A π n h hne hgen b :=
  Proj.map (boundaryVeroneseTransition A π n h (exactVeroneseStep A π hne hgen n h) f)
    (boundaryVeroneseTransition_irrelevant A π hne hgen n h f)

/-- The original stage Proj maps commute with the original evaluations into the candidate. -/
@[reassoc]
theorem boundaryVeroneseProjTransition_toCompatible {a b : ℕ} (f : a ⟶ b) :
    boundaryVeroneseProjTransition A π hne hgen n h f ≫ boundaryVeroneseProjToCompatible A π n h
    hne hgen b =
      boundaryVeroneseProjToCompatible A π n h hne hgen a := by
  unfold boundaryVeroneseProjTransition boundaryVeroneseProjToCompatible
  simp only [← Proj.map_comp, boundaryVeroneseTransition_evaluation]

/-- Each standard chart map is localization of the specified original stage restriction. -/
@[reassoc]
theorem boundaryVeroneseProjTransition_away {a b : ℕ} (f : a ⟶ b) (d : ℕ) (hd : 0 < d)
    (s : boundaryVeroneseRing A π n h (exactVeroneseStep A π hne hgen n h) b)
    (hs : s ∈ boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) b d) :
    Proj.awayι (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) a)
        (boundaryVeroneseTransition A π n h (exactVeroneseStep A π hne hgen n h) f s)
        ((boundaryVeroneseTransition A π n h _ f).map_mem hs) hd ≫
      boundaryVeroneseProjTransition A π hne hgen n h f =
        Spec.map (CommRingCat.ofHom
          (Away.map (boundaryVeroneseTransition A π n h (exactVeroneseStep A π hne hgen n h) f)
    s)) ≫
            Proj.awayι (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) b) s hs
    hd :=
  Proj.awayι_comp_map (boundaryVeroneseTransition A π n h _ f)
    (boundaryVeroneseTransition_irrelevant A π hne hgen n h f) hd s hs

end FLT.Mazur.PolygonArithmeticStages
