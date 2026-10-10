/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesContraction
public import FLT.Mazur.BlowupReesGeneratorCover
public import FLT.Mazur.BlowupReesRatio
public import FLT.Mazur.PrincipalAffineRefinement

/-!
# The original principal open inside Rees Proj

Inverting an element of the center identifies an actual open of Rees Proj
with the original principal open. The full contraction preimage lies in
this open, rather than merely containing the displayed section.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.BlowupRees
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type*} [CommRing A] (I : Ideal A) (f : A) (hf : f ∈ I)

/-- The original principal open is the denominator open of its fraction chart. -/
def originalOpenIso : Spec (.of (Localization.Away f)) ≅
    Spec (.of (BlowupFractionChart.DenominatorOpen I f)) :=
  Scheme.Spec.mapIso (BlowupFractionChart.denominatorOpenEquiv I f).toRingEquiv.toCommRingCatIso.op

/-- Include the unchanged original principal open in the actual Rees scheme. -/
def originalOpenInclusion : Spec (.of (Localization.Away f)) ⟶ proj I :=
  (originalOpenIso I f).hom ≫
    PrincipalAffineRefinement.inclusion (BlowupFractionChart.denominator I f) ≫
      fractionChartInclusion I f hf

instance originalOpenInclusion_isOpenImmersion :
    IsOpenImmersion (originalOpenInclusion I f hf) := by
  unfold originalOpenInclusion
  infer_instance

/-- The unchanged open retains all original base functions under contraction. -/
@[reassoc] theorem originalOpenInclusion_contraction :
    originalOpenInclusion I f hf ≫ contraction I = PrincipalAffineRefinement.inclusion f := by
  rw [originalOpenInclusion, Category.assoc, Category.assoc, fractionChartInclusion_contraction]
  change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (BlowupFractionChart.denominatorOpenEquiv I f).commutes a

/-- A point over D(f) lies in the f-generator chart, including on every other chart. -/
theorem mem_generatorOpen_of_contraction (z : proj I)
    (hz : contraction I z ∈ PrimeSpectrum.basicOpen f) : z ∈ generatorOpen I f hf := by
  obtain ⟨g, p, rfl⟩ := exists_fractionChart I (fun g : I => (g : A))
    (fun g => g.property) (by simp) z
  have hp : algebraMap A (BlowupFractionChart.chart I g) f ∉ p.asIdeal := by
    change (fractionChartInclusion I g g.property ≫ contraction I) p ∈
      PrimeSpectrum.basicOpen f at hz
    rw [fractionChartInclusion_contraction] at hz
    exact hz
  change p ∈ fractionChartInclusion I g g.property ⁻¹ᵁ generatorOpen I f hf
  rw [fractionChartInclusion_preimage]
  intro hr
  apply hp
  rw [← BlowupFractionChart.denominator_mul_ratio I g f hf]
  exact p.asIdeal.mul_mem_left _ hr

/-- The entire inverse image of D(f) is the unchanged original principal open. -/
theorem originalOpen_preimage :
    contraction I ⁻¹' Set.range (PrincipalAffineRefinement.inclusion f) =
      Set.range (originalOpenInclusion I f hf) := by
  apply Set.Subset.antisymm
  · intro z hz
    rw [PrincipalAffineRefinement.range_inclusion] at hz
    have hm := mem_generatorOpen_of_contraction I f hf z hz
    rw [← fractionChartInclusion_range] at hm
    obtain ⟨p, rfl⟩ := hm
    have hp : p ∈ Set.range
        (PrincipalAffineRefinement.inclusion (BlowupFractionChart.denominator I f)) := by
      rw [PrincipalAffineRefinement.range_inclusion]
      change (fractionChartInclusion I f hf ≫ contraction I) p ∈
        PrimeSpectrum.basicOpen f at hz
      rw [fractionChartInclusion_contraction] at hz
      exact hz
    obtain ⟨o, rfl⟩ := hp
    refine ⟨(originalOpenIso I f).inv o, ?_⟩
    simp only [originalOpenInclusion, ← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]
  · rintro _ ⟨o, rfl⟩
    exact ⟨o, (congrArg (fun g => g o) (originalOpenInclusion_contraction I f hf)).symm⟩

/-- The full base change to D(f) is the identity of that original open. -/
theorem originalOpen_isPullback :
    IsPullback (𝟙 _) (originalOpenInclusion I f hf)
      (PrincipalAffineRefinement.inclusion f) (contraction I) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (by simp [originalOpenInclusion_contraction])
  exact TopologicalSpace.Opens.ext (originalOpen_preimage I f hf)

end FLT.Mazur.BlowupRees
