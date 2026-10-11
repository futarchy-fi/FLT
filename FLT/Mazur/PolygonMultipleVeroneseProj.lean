/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseMultipleExactness
public import FLT.Mazur.PolygonStageVeroneseGrading
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Original stage maps into every common retained Proj

Homogeneous lifting proves irrelevant-ideal coverage for every positive multiple
of the exact step. The induced scheme map uses the actual stage evaluation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization
open scoped DirectSum
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (q : ℕ) (hq : exactVeroneseStep K n h ∣ q)

attribute [local irreducible] compatibleEval boundaryLine family

variable [NeZero q]

/-- The positive common step gives the original stage its retained grading. -/
local instance multipleStageGradedRing (m : ℕ) : GradedRing (boundaryVeroneseGrade K n h q m) :=
  boundaryVeroneseGradedRing K n h q (NeZero.pos q) m

include hq

omit [NeZero q] in
/-- Every original homogeneous stage section lifts at any multiple of the exact step. -/
theorem multipleVeroneseEvaluation_homogeneous_surjective (m d : ℕ)
    (s : boundaryVeroneseGrade K n h q m d) :
    ∃ t : compatibleVeroneseDegree K n h q d,
      boundaryVeroneseEvaluation K n h q m (DirectSum.of _ d t) = s := by
  obtain ⟨t, ht⟩ := multipleVeroneseDegree_surjective K n h q hq d m
    ⟨s.val.val, s.property⟩
  refine ⟨t, Subtype.ext ?_⟩
  rw [boundaryVeroneseEvaluation_of]
  exact congrArg Subtype.val ht

/-- The original evaluations cover the whole stage Proj at a common retained step. -/
theorem multipleVeroneseEvaluation_irrelevant (m : ℕ) :
    (boundaryVeroneseGrade K n h q m)₊ ≤
      (compatibleVeroneseGrade K n h q)₊.map (boundaryVeroneseEvaluation K n h q m) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (toIdeal_irrelevant_le _).mpr
  intro d hd s hs
  obtain ⟨t, ht⟩ := multipleVeroneseEvaluation_homogeneous_surjective K n h q hq m d ⟨s, hs⟩
  change boundaryVeroneseEvaluation K n h q m (DirectSum.of _ d t) = s at ht
  rw [← ht]
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ hd ⟨t, rfl⟩)

/-- The constructed stage Proj morphism at any positive common multiple. -/
def multipleVeroneseProjToCompatible (m : ℕ) :
    Proj (boundaryVeroneseGrade K n h q m) ⟶ Proj (compatibleVeroneseGrade K n h q) :=
  Proj.map (boundaryVeroneseEvaluation K n h q m)
    (multipleVeroneseEvaluation_irrelevant K n h q hq m)

/-- Basic-open pullback retains the original evaluation at the common step. -/
theorem multipleVeroneseProjToCompatible_basicOpen (m : ℕ)
    (s : CompatibleVeroneseSections K n h q) :
    multipleVeroneseProjToCompatible K n h q hq m ⁻¹ᵁ
        Proj.basicOpen (compatibleVeroneseGrade K n h q) s =
      Proj.basicOpen (boundaryVeroneseGrade K n h q m)
        (boundaryVeroneseEvaluation K n h q m s) := rfl

/-- Each common-step affine chart uses the localization of the original evaluation. -/
@[reassoc]
theorem multipleVeroneseProjToCompatible_away (m d : ℕ) (hd : 0 < d)
    (s : CompatibleVeroneseSections K n h q) (hs : s ∈ compatibleVeroneseGrade K n h q d) :
    Proj.awayι (boundaryVeroneseGrade K n h q m)
        (boundaryVeroneseEvaluation K n h q m s)
        ((boundaryVeroneseEvaluation K n h q m).map_mem hs) hd ≫
      multipleVeroneseProjToCompatible K n h q hq m =
        Spec.map (CommRingCat.ofHom (Away.map (boundaryVeroneseEvaluation K n h q m) s)) ≫
          Proj.awayι (compatibleVeroneseGrade K n h q) s hs hd :=
  Proj.awayι_comp_map (boundaryVeroneseEvaluation K n h q m)
    (multipleVeroneseEvaluation_irrelevant K n h q hq m) hd s hs

end FLT.Mazur.PolygonInfinitesimalStages
