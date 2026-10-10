/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleRetainedChartGeneration
public import FLT.Mazur.GradedProjEventualGenerationCover

/-!
# Original affine section charts cover the whole retained Proj

Proper coherent vanishing makes the same affine section generators contain
all sufficiently high retained degrees in their ideal. Their homogeneous
basic opens therefore cover the entire retained projective spectrum.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.ProperAmpleRetainedChartCover

open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionCover
open SectionRetainedChartComparison

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

include f

/-- One original affine generator family covers both the original scheme and its retained Proj. -/
theorem exists_cover (hA : AmpleLineBundle L) (hq : 0 < q) :
    ∃ (I : Type) (_ : Fintype I) (a : ℕ) (_ : 0 < a)
      (s : I → Γ(tensorPower L (q * a), ⊤)),
      (∀ i, IsAffineOpen (chart s i)) ∧ (⨆ i, chart s i = ⊤) ∧
      ⨆ i, Proj.basicOpen (RetainedSubringGrading.grade (grade L ⊤) q)
        (insertion L q a (s i)) = ⊤ := by
  classical
  obtain ⟨I, hI, a, ha, s, haff, hcover, B, hB⟩ :=
    hA.retained_affine_multiplication_generators f q hq
  let _ := hI
  refine ⟨I, hI, a, ha, s, haff, hcover, ?_⟩
  apply GradedProjEventualGenerationCover.iSup_basicOpen_eq_top _ _ (a + B)
  intro d hd z hz
  obtain ⟨b, rfl⟩ : ∃ b, d = a + b := ⟨d - a, by omega⟩
  change z.val ∈ grade L ⊤ (q * (a + b)) at hz
  obtain ⟨v, hv⟩ := hz
  obtain ⟨t, ht⟩ := hB b (by omega) v
  have he : z = ∑ i, insertion L q a (s i) * insertion L q b (t i) := by
    apply Subtype.ext
    change z.val = (RetainedSubringGrading.ring (grade L ⊤) q).subtype
      (∑ i, insertion L q a (s i) * insertion L q b (t i))
    simp only [map_sum, map_mul]
    exact hv.symm.trans ht
  rw [he]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))

end FLT.Mazur.ProperAmpleRetainedChartCover
