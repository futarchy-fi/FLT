/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonAdicQuotientGrading
public import FLT.Mazur.PolygonVeroneseProperProj
public import FLT.Mazur.GradedProjRingEquiv

/-!
# Proj maps retaining the actual stage reductions

The original stage ring and the actual adic quotient have isomorphic Proj.
The stage map to the compatible Proj retains the original evaluation on all
homogeneous-localization charts. The base-change assertion is separate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Proj of the original retained stage sections with their original multiplication. -/
def boundaryExactVeroneseProj (m : ℕ) : Scheme :=
  Proj (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m)

/-- The actual adic reduction induces an isomorphism on the graded projective spectra. -/
def exactVeroneseReductionProjIso (m : ℕ) :
    boundaryExactVeroneseProj K n h m ≅ Proj (exactVeroneseQuotientGrade K n h m) :=
  GradedProjRingEquiv.iso _ _ (exactVeroneseAdicReduction K n h m)
    (exactVeroneseAdicReduction_mem_iff K n h m)

/-- Original positive compatible degrees generate the irrelevant ideal of each stage. -/
theorem boundaryVeroneseEvaluation_irrelevant (m : ℕ) :
    (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m)₊ ≤
      (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))₊.map
        (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (toIdeal_irrelevant_le _).mpr
  intro d hd s hs
  obtain ⟨t, ht⟩ := boundaryVeroneseEvaluation_homogeneous_surjective K n h m d ⟨s, hs⟩
  change boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m
    (DirectSum.of _ d t) = s at ht
  rw [← ht]
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ hd ⟨t, rfl⟩)

/-- The actual evaluation defines the stage map into the proper compatible Proj. -/
def boundaryVeroneseProjToCompatible (m : ℕ) :
    boundaryExactVeroneseProj K n h m ⟶ exactVeroneseProj K n h :=
  Proj.map (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m)
    (boundaryVeroneseEvaluation_irrelevant K n h m)

/-- Pulling back a compatible basic open uses its original stage evaluation. -/
theorem boundaryVeroneseProjToCompatible_basicOpen (m : ℕ)
    (s : CompatibleVeroneseSections K n h (exactVeroneseStep K n h)) :
    boundaryVeroneseProjToCompatible K n h m ⁻¹ᵁ
        Proj.basicOpen (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) s =
      Proj.basicOpen (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m)
        (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m s) := rfl

/-- On every standard chart the stage morphism is the original localization of evaluation. -/
@[reassoc]
theorem boundaryVeroneseProjToCompatible_away (m d : ℕ) (hd : 0 < d)
    (s : CompatibleVeroneseSections K n h (exactVeroneseStep K n h))
    (hs : s ∈ compatibleVeroneseGrade K n h (exactVeroneseStep K n h) d) :
    Proj.awayι (boundaryVeroneseGrade K n h (exactVeroneseStep K n h) m)
        (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m s)
        ((boundaryVeroneseEvaluation K n h _ m).map_mem hs) hd ≫
      boundaryVeroneseProjToCompatible K n h m =
        Spec.map (CommRingCat.ofHom
          (Away.map (boundaryVeroneseEvaluation K n h (exactVeroneseStep K n h) m) s)) ≫
            Proj.awayι (compatibleVeroneseGrade K n h (exactVeroneseStep K n h)) s hs hd :=
  Proj.awayι_comp_map (boundaryVeroneseEvaluation K n h _ m)
    (boundaryVeroneseEvaluation_irrelevant K n h m) hd s hs

end FLT.Mazur.PolygonInfinitesimalStages
