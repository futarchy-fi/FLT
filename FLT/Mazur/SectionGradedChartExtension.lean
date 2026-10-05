/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedPowers
public import FLT.Mazur.AmpleChartSectionExtension

/-!
# Chart extension in the actual graded section ring

Extension from a finite affine generator cover produces a numerator whose
restriction is the given chart function times a genuine graded-ring power.
The nested tensor power is transported by the exponent-multiplication
isomorphism, and its restriction is identified by naturality.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u v
namespace FLT.Mazur.SectionGradedChartExtension
open FCurve ModuleLineBundleTensorPullback SectionCover
open SectionGradedSum SectionGradedPowers
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules) {ι : Type v}

/-- An affine chart function is a homogeneous numerator divided by a power of its generator. -/
theorem numerator [Finite ι] (d : ℕ) (s : ι → Γ(tensorPower L d, ⊤))
    (haff : ∀ j, IsAffineOpen (chart s j)) (hcover : ⨆ j, chart s j = ⊤)
    (i : ι) (a : Γ(X, chart s i)) :
    ∃ (N : ℕ) (t : Γ(tensorPower L (d * N), ⊤)),
      restrictRingHom L (chart s i) (homOfLE le_top) (of L ⊤ (d * N) t) =
        a • (restrictRingHom L (chart s i) (homOfLE le_top) (of L ⊤ d (s i))) ^ N := by
  obtain ⟨N, σ, hσ⟩ := sectionCover_extension s haff hcover i a
  refine ⟨N, (tensorPowerMulIso L d N).hom.app ⊤ σ, ?_⟩
  rw [show restrictRingHom L (chart s i) (homOfLE le_top)
      (of L ⊤ (d * N) ((tensorPowerMulIso L d N).hom.app ⊤ σ)) =
      of L (chart s i) (d * N) ((tensorPower L (d * N)).presheaf.map
        (homOfLE (show chart s i ≤ ⊤ from le_top)).op
          ((tensorPowerMulIso L d N).hom.app ⊤ σ)) from restrict_of L _ _ _]
  have hn := congrArg (fun f ↦ f σ)
    ((tensorPowerMulIso L d N).hom.mapPresheaf.naturality
      (homOfLE (show chart s i ≤ ⊤ from le_top)).op)
  change (tensorPowerMulIso L d N).hom.app (chart s i)
    ((tensorPower (tensorPower L d) N).presheaf.map _ σ) =
      (tensorPower L (d * N)).presheaf.map _
        ((tensorPowerMulIso L d N).hom.app ⊤ σ) at hn
  rw [← hn, hσ, Hom.app_smul, _root_.map_smul, of_tensorPower]
  exact congrArg (fun z ↦ a • z ^ N) (restrict_of L _ d (s i)).symm

/-- Ample line bundles have an affine cover with actual graded-ring numerators. -/
theorem ample_numerators (hL : AmpleLineBundle L) :
    ∃ (ι : Type u) (_ : Finite ι) (d : ℕ) (_ : 0 < d)
      (s : ι → Γ(tensorPower L d, ⊤)),
      (∀ i, IsAffineOpen (chart s i)) ∧ (⨆ i, chart s i) = ⊤ ∧
      ∀ (i : ι) (a : Γ(X, chart s i)),
        ∃ (N : ℕ) (t : Γ(tensorPower L (d * N), ⊤)),
          restrictRingHom L (chart s i) (homOfLE le_top) (of L ⊤ (d * N) t) =
            a • (restrictRingHom L (chart s i) (homOfLE le_top) (of L ⊤ d (s i))) ^ N := by
  obtain ⟨ι, hι, d, hd, s, haff, hcover⟩ := hL.common_degree_section_cover
  let := hι
  exact ⟨ι, hι, d, hd, s, haff, hcover, numerator L d s haff hcover⟩

end FLT.Mazur.SectionGradedChartExtension
