/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonVeroneseMultipleInclusion
public import FLT.Mazur.GradedLocalizationDegreeMap
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Actual affine chart comparisons for multiple Veronese steps

The inclusion of retained algebras induces isomorphisms of their homogeneous
localizations. Powers of the original homogeneous sections supply common charts.
-/

@[expose] public noncomputable section
open AlgebraicGeometry HomogeneousLocalization
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (R : Type) [CommRing R] (n : ℕ) (h : 2 ≤ n) (q r : ℕ) [NeZero q]

/-- The original inclusion maps homogeneous fractions even though it changes the degree. -/
def multipleVeroneseChartMap (s : CompatibleVeroneseSections R n h (q * r)) :
    Away (compatibleVeroneseGrade R n h (q * r)) s →+*
      Away (compatibleVeroneseGrade R n h q) (multipleVeroneseInclusion R n h q r s) :=
  GradedLocalizationDegreeMap.awayMap _ _ (multipleVeroneseInclusion R n h q r) r
    (multipleVeroneseInclusion_mem R n h q r) s

/-- Injectivity of the original retained inclusion is retained on each actual chart. -/
theorem multipleVeroneseChartMap_injective (hr : 0 < r)
    (s : CompatibleVeroneseSections R n h (q * r)) :
    Function.Injective (multipleVeroneseChartMap R n h q r s) :=
  GradedLocalizationDegreeMap.awayMap_injective _ _ _ r
    (multipleVeroneseInclusion_mem R n h q r)
    (multipleVeroneseInclusion_injective R n h q r hr) s

/-- Every homogeneous chart numerator already belongs to a common retained degree. -/
theorem multipleVeroneseChartMap_surjective (d : ℕ)
    (s : CompatibleVeroneseSections R n h (q * r))
    (hs : s ∈ compatibleVeroneseGrade R n h (q * r) d) :
    Function.Surjective (multipleVeroneseChartMap R n h q r s) :=
  GradedLocalizationDegreeMap.awayMap_surjective _ _ _ r
    (multipleVeroneseInclusion_mem R n h q r) hs
    (fun k ↦ multipleVeroneseInclusion_homogeneous_surjective R n h q r (k * d))

/-- The standard affine charts are isomorphic through the actual common-degree inclusion. -/
def multipleVeroneseChartIso (hr : 0 < r) (d : ℕ)
    (s : CompatibleVeroneseSections R n h (q * r))
    (hs : s ∈ compatibleVeroneseGrade R n h (q * r) d) :
    Away (compatibleVeroneseGrade R n h (q * r)) s ≃+*
      Away (compatibleVeroneseGrade R n h q) (multipleVeroneseInclusion R n h q r s) :=
  RingEquiv.ofBijective (multipleVeroneseChartMap R n h q r s)
    ⟨multipleVeroneseChartMap_injective R n h q r hr s,
      multipleVeroneseChartMap_surjective R n h q r d s hs⟩

/-- Every original homogeneous basic open is the image-denominator chart of a common degree. -/
theorem multipleVeronese_common_basicOpen (hr : 0 < r) (d : ℕ)
    (s : CompatibleVeroneseSections R n h q) (hs : s ∈ compatibleVeroneseGrade R n h q d) :
    ∃ t ∈ compatibleVeroneseGrade R n h (q * r) d,
      Proj.basicOpen (compatibleVeroneseGrade R n h q)
        (multipleVeroneseInclusion R n h q r t) =
          Proj.basicOpen (compatibleVeroneseGrade R n h q) s := by
  have hp : s ^ r ∈ compatibleVeroneseGrade R n h q (r * d) :=
    SetLike.pow_mem_graded r hs
  obtain ⟨t, ht, he⟩ := multipleVeroneseInclusion_homogeneous_surjective R n h q r d (s ^ r) hp
  refine ⟨t, ht, ?_⟩
  rw [he, Proj.basicOpen_pow _ s r hr]

/-- Common retained denominators cover the whole original Proj, not just its closed fiber. -/
theorem multipleVeronese_common_charts_cover (hr : 0 < r) :
    (⨆ i : Σ d : PNat, compatibleVeroneseGrade R n h (q * r) d,
      Proj.basicOpen (compatibleVeroneseGrade R n h q)
        (multipleVeroneseInclusion R n h q r i.2)) = ⊤ := by
  apply top_unique
  intro z _
  let i := (Proj.affineOpenCover (compatibleVeroneseGrade R n h q)).idx z
  have hi : z ∈ Proj.basicOpen (compatibleVeroneseGrade R n h q) i.2 := by
    have hz := (Proj.affineOpenCover (compatibleVeroneseGrade R n h q)).covers z
    change z ∈
      (Proj.awayι (compatibleVeroneseGrade R n h q) i.2.val
        i.2.property i.1.property).opensRange at hz
    rwa [Proj.opensRange_awayι] at hz
  obtain ⟨t, ht, he⟩ := multipleVeronese_common_basicOpen R n h q r hr i.1 i.2 i.2.property
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨⟨i.1, ⟨t, ht⟩⟩, ?_⟩
  rw [he]
  exact hi

end FLT.Mazur.PolygonInfinitesimalStages
