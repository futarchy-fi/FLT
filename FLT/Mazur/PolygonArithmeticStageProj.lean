/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticQuotientGrading
public import FLT.Mazur.PolygonArithmeticProperProj
public import FLT.Mazur.GradedProjRingEquiv

/-!
# Proj maps retaining the actual stage reductions

The original stage ring and the actual adic quotient have isomorphic Proj.
The stage map to the compatible Proj retains the original evaluation on all
homogeneous-localization charts. The base-change assertion is separate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A : Type) [CommRing A] (π : A) (n : ℕ) (h : 2 ≤ n)
  [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  (hne : π ≠ 0) (hgen : IsLocalRing.maximalIdeal A = ideal A π) [NeZero n]

/-- Proj of the original retained stage sections with their original multiplication. -/
def boundaryExactVeroneseProj (m : ℕ) : Scheme :=
  Proj (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m)

/-- The actual adic reduction induces an isomorphism on the graded projective spectra. -/
def exactVeroneseReductionProjIso (m : ℕ) :
    boundaryExactVeroneseProj A π n h hne hgen m ≅ Proj (exactVeroneseQuotientGrade A π n h hne
      hgen m) :=
  GradedProjRingEquiv.iso _ _ (exactVeroneseAdicReduction A π n h hne hgen m)
    (exactVeroneseAdicReduction_mem_iff A π n h hne hgen m)

/-- Original positive compatible degrees generate the irrelevant ideal of each stage. -/
theorem boundaryVeroneseEvaluation_irrelevant (m : ℕ) :
    (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m)₊ ≤
      (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h))₊.map
        (boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (toIdeal_irrelevant_le _).mpr
  intro d hd s hs
  obtain ⟨t, ht⟩ := boundaryVeroneseEvaluation_homogeneous_surjective A π n h hne hgen m d ⟨s, hs⟩
  change boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m
    (DirectSum.of _ d t) = s at ht
  rw [← ht]
  exact Ideal.mem_map_of_mem _ (mem_irrelevant_of_mem _ hd ⟨t, rfl⟩)

/-- The actual evaluation defines the stage map into the proper compatible Proj. -/
def boundaryVeroneseProjToCompatible (m : ℕ) :
    boundaryExactVeroneseProj A π n h hne hgen m ⟶ exactVeroneseProj A π n h hne hgen :=
  Proj.map (boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m)
    (boundaryVeroneseEvaluation_irrelevant A π n h hne hgen m)

/-- Pulling back a compatible basic open uses its original stage evaluation. -/
theorem boundaryVeroneseProjToCompatible_basicOpen (m : ℕ)
    (s : CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h)) :
    boundaryVeroneseProjToCompatible A π n h hne hgen m ⁻¹ᵁ
        Proj.basicOpen (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h)) s =
      Proj.basicOpen (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m)
        (boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m s) := rfl

/-- On every standard chart the stage morphism is the original localization of evaluation. -/
@[reassoc]
theorem boundaryVeroneseProjToCompatible_away (m d : ℕ) (hd : 0 < d)
    (s : CompatibleVeroneseSections A π n h (exactVeroneseStep A π hne hgen n h))
    (hs : s ∈ compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) d) :
    Proj.awayι (boundaryVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h) m)
        (boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m s)
        ((boundaryVeroneseEvaluation A π n h _ m).map_mem hs) hd ≫
      boundaryVeroneseProjToCompatible A π n h hne hgen m =
        Spec.map (CommRingCat.ofHom
          (Away.map (boundaryVeroneseEvaluation A π n h (exactVeroneseStep A π hne hgen n h) m)
      s)) ≫
            Proj.awayι (compatibleVeroneseGrade A π n h (exactVeroneseStep A π hne hgen n h)) s
      hs hd :=
  Proj.awayι_comp_map (boundaryVeroneseEvaluation A π n h _ m)
    (boundaryVeroneseEvaluation_irrelevant A π n h hne hgen m) hd s hs

end FLT.Mazur.PolygonArithmeticStages
