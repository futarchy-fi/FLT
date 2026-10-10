/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleRetainedSectionCover
public import FLT.Mazur.AmpleVeroneseMultiplication
public import FLT.Mazur.SectionRetainedChartComparison

/-!
# Original affine retained charts eventually generate sections

Choose the retained generators from an actual affine cover. Proper coherent
vanishing then expresses every sufficiently high retained section as a sum
of products with those same generators, preserving their original charts.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open ProjectiveSpace ModuleLineBundleTensorPullback SectionGradedSum

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}

/-- Affine retained generators cover the original scheme and generate all high degrees. -/
theorem AmpleLineBundle.retained_affine_multiplication_generators
    (f : X ⟶ Spec (.of R)) [IsProper f] {L : X.Modules} (hL : AmpleLineBundle L)
    (q : ℕ) (hq : 0 < q) :
    ∃ (I : Type) (_ : Fintype I) (a : ℕ) (_ : 0 < a)
      (s : I → Γ(tensorPower L (q * a), ⊤)),
      (∀ i, IsAffineOpen (SectionCover.chart s i)) ∧ (⨆ i, SectionCover.chart s i = ⊤) ∧
      ∃ B : ℕ, ∀ d ≥ B, ∀ v : Γ(tensorPower L (q * (a + d)), ⊤),
        ∃ t : I → Γ(tensorPower L (q * d), ⊤),
          of L ⊤ (q * (a + d)) v =
            ∑ i, of L ⊤ (q * a) (s i) * of L ⊤ (q * d) (t i) := by
  obtain ⟨I, hI, a, ha, s, haff, hcover⟩ := hL.retained_section_cover q hq
  let _ := hI
  let _ := Fintype.ofFinite I
  have hs : Epi (globalEvaluation (tensorPower L (q * a)) s) :=
    globalEvaluation_epi_of_sectionHom_isIso s (SectionCover.chart s) hcover id
      (fun i ↦ sectionHom_generatorOpen_isIso (tensorPower L (q * a)) (s i))
  let _ := (hL.2.1.tensorPower (q * a)).isFinitePresentation
  obtain ⟨B, hB⟩ := ample_twisted_sections_surjective f hL (globalEvaluation _ s)
  refine ⟨I, inferInstance, a, ha, s, haff, hcover, B, fun d hd ↦ ?_⟩
  have hd' : B ≤ q * d := hd.trans (Nat.le_mul_of_pos_left d hq)
  rw [Nat.mul_add]
  intro v
  obtain ⟨t, ht⟩ := section_mul_sum_of_twistedEvaluation_surjective L (q * a) (q * d)
    s (hB (q * d) hd') v
  refine ⟨t, ?_⟩
  rw [ht, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (mul_of L ⊤ (q * a) (q * d) (s i) (t i)).symm

end FLT.Mazur.FCurve
