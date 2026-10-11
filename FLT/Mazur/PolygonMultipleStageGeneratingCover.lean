/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPositiveRetainedStage

/-!
# Original stage covers from compatible homogeneous sections

Homogeneous lifting replaces every original ample generator by an actual
compatible section, retaining its invertible line coordinate on the same cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionRetainedChartComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] compatibleEval boundaryLine family
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (q : ℕ) [NeZero q] (hq : exactVeroneseStep K n h ∣ q)

include hq

/-- Compatible homogeneous sections give a genuine generating cover of the original stage. -/
theorem exists_multipleStageGeneratingCover (m : ℕ) :
    ∃ (𝒰 : Scheme.OpenCover.{0} (family K m n h).left)
      (e : ∀ i, (pullback (𝒰.f i)).obj (boundaryLine K m n h) ≅ structureModule (𝒰.X i))
      (d : 𝒰.I₀ → ℕ) (s : 𝒰.I₀ → CompatibleVeroneseSections K n h q),
      (∀ i, s i ∈ compatibleVeroneseGrade K n h q (d i)) ∧ (∀ i, 0 < d i) ∧
      ∀ i, IsUnit (SectionGradedProjChart.ringHom (𝒰.f i) (boundaryLine K m n h) (e i)
        (compatibleVeroneseEval K n h q m (s i))) := by
  obtain ⟨𝒰, e, d, s, hd, hu⟩ := SectionRetainedProjConstruction.exists_generating_cover
    (boundaryLine K m n h) q (boundaryPositiveRetainedGenerated K n h q m)
  have hl (i : 𝒰.I₀) := multipleVeroneseEvaluation_homogeneous_surjective K n h q hq m (d i)
    ⟨insertion (boundaryLine K m n h) q (d i) (s i),
      insertion_mem (boundaryLine K m n h) q (d i) (s i)⟩
  choose t ht using hl
  refine ⟨𝒰, e, d, fun i ↦ DirectSum.of _ (d i) (t i), fun i ↦ ⟨t i, rfl⟩, hd, ?_⟩
  intro i
  have he := congrArg Subtype.val (ht i)
  change compatibleVeroneseEval K n h q m (DirectSum.of _ (d i) (t i)) =
    of (boundaryLine K m n h) ⊤ (q * d i) (s i) at he
  rw [he]
  exact hu i

end FLT.Mazur.PolygonInfinitesimalStages
