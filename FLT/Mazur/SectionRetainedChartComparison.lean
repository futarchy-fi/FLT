/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RetainedSubringLocalization
public import FLT.Mazur.SectionGradedChartIsomorphism
public import FLT.Mazur.SectionGradedChartRatios

/-!
# Retained section fractions as actual chart functions

The retained homogeneous chart is identified with the original ring of
functions on an affine generator chart. The comparison keeps the original
numerator-denominator equation and commutes with restriction of functions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization Scheme.Modules

namespace FLT.Mazur.SectionRetainedChartComparison

open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionCover

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

/-- The original insertion of a retained homogeneous section in its actual subring. -/
def insertion (d : ℕ) (s : Γ(tensorPower L (q * d), ⊤)) :
    RetainedSubringGrading.ring (grade L ⊤) q :=
  ⟨of L ⊤ (q * d) s, Subring.subset_closure (Set.mem_iUnion.mpr ⟨d, s, rfl⟩)⟩

omit [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)] in
/-- A retained insertion belongs to its original reindexed degree. -/
theorem insertion_mem (d : ℕ) (s : Γ(tensorPower L (q * d), ⊤)) :
    insertion L q d s ∈ RetainedSubringGrading.grade (grade L ⊤) q d := ⟨s, rfl⟩

/-- Evaluate retained fractions on an original generator subopen. -/
def toFunctions (d : ℕ) (s : Γ(tensorPower L (q * d), ⊤))
    (U : X.Opens) (hU : U ≤ sectionGeneratorOpen (tensorPower L (q * d)) s) :
    Away (RetainedSubringGrading.grade (grade L ⊤) q) (insertion L q d s) →+* Γ(X, U) :=
  (SectionGradedChartComparison.toFunctions L (q * d) s U hU).comp
    (RetainedSubringLocalization.inclusion (grade L ⊤) q (insertion L q d s))

/-- Retained homogeneous localization recovers an actual affine generator chart. -/
def ringEquiv {ι : Type*} [Finite ι] (d : ℕ)
    (s : ι → Γ(tensorPower L (q * d), ⊤))
    (haff : ∀ j, IsAffineOpen (chart s j)) (hcover : ⨆ j, chart s j = ⊤) (i : ι) :
    Away (RetainedSubringGrading.grade (grade L ⊤) q) (insertion L q d (s i)) ≃+*
      Γ(X, chart s i) :=
  (RetainedSubringLocalization.ringEquiv (grade L ⊤) q _ (insertion_mem L q d (s i))).trans
    (SectionGradedChartIsomorphism.ringEquiv L (q * d) s haff hcover i)

/-- The chart isomorphism is the actual comparison on every retained fraction. -/
theorem ringEquiv_apply {ι : Type*} [Finite ι] (d : ℕ)
    (s : ι → Γ(tensorPower L (q * d), ⊤))
    (haff : ∀ j, IsAffineOpen (chart s j)) (hcover : ⨆ j, chart s j = ⊤) (i : ι)
    (z : Away (RetainedSubringGrading.grade (grade L ⊤) q) (insertion L q d (s i))) :
    ringEquiv L q d s haff hcover i z = toFunctions L q d (s i) (chart s i) le_rfl z := rfl

/-- Restricting a retained chart function agrees with evaluating on the smaller generator open. -/
theorem toFunctions_restrict (d : ℕ) (s : Γ(tensorPower L (q * d), ⊤))
    {U V : X.Opens} (hVU : V ≤ U)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L (q * d)) s) :
    (X.presheaf.map (homOfLE hVU).op).hom.comp (toFunctions L q d s U hU) =
      toFunctions L q d s V (hVU.trans hU) := by
  unfold toFunctions
  rw [← RingHom.comp_assoc, SectionGradedChartRatios.toFunctions_restrict]

end FLT.Mazur.SectionRetainedChartComparison
