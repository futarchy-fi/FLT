/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperNeighborhoodFiniteUnion
public import FLT.Mazur.UnramifiedSectionImmersion

/-!
# Proper neighborhoods constructed from actual sections

An open section is an isomorphism onto its open image. Thus its image is
proper over the unchanged target, even if the ambient morphism is not proper.
Finite families construct one finite etale open containing all their images.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SectionProperNeighborhood
universe u v
section Section
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)

include hs

/-- The projection of an open section image is an actual isomorphism. -/
theorem projection_isIso [IsOpenImmersion s] : IsIso (s.opensRange.ι ≫ f) := by
  let e := IsOpenImmersion.isoOfRangeEq s s.opensRange.ι (by
    rw [Scheme.Opens.range_ι]; rfl)
  have he : e.hom ≫ s.opensRange.ι = s := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h : s.opensRange.ι ≫ f = e.inv := by
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, he, hs, e.hom_inv_id]
  rw [h]
  infer_instance

/-- Every point on an open section has a constructed proper neighborhood. -/
theorem range_subset_locus [IsOpenImmersion s] :
    Set.range s ⊆ ProperNeighborhoodAtlas.locus f := by
  let _ := projection_isIso f s hs
  intro x hx
  exact (ProperNeighborhoodAtlas.mem_locus_iff f x).mpr
    ⟨s.opensRange, hx, inferInstance⟩

/-- Etaleness supplies the open immersion for any actual section. -/
theorem etale_range_subset_locus [Etale f] :
    Set.range s ⊆ ProperNeighborhoodAtlas.locus f := by
  let _ := UnramifiedSectionImmersion.isOpenImmersion f s hs
  exact range_subset_locus f s hs

end Section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  {I : Type v} [Finite I] (a : I → (Y ⟶ X))
  (ha : ∀ i, a i ≫ f = 𝟙 Y) [Etale f] [IsSeparated f]

include ha

/-- The finite union of section images is proper over the same unchanged ground. -/
theorem union_isProper :
    let _ (i : I) := UnramifiedSectionImmersion.isOpenImmersion f (a i) (ha i)
    IsProper ((⨆ i, (a i).opensRange).ι ≫ f) := by
  let _ (i : I) := UnramifiedSectionImmersion.isOpenImmersion f (a i) (ha i)
  let _ (i : I) : IsIso ((a i).opensRange.ι ≫ f) := projection_isIso f (a i) (ha i)
  exact ProperNeighborhoodAtlas.finiteUnion_isProper f (fun i ↦ (a i).opensRange)

/-- Construct a single finite etale open with exactly the union of the section images. -/
theorem exists_finite_open :
    ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ Etale (U.ι ≫ f) ∧
      U ≤ ProperNeighborhoodAtlas.locus f ∧
      ∀ x : X, x ∈ U ↔ ∃ i, a i (f x) = x := by
  let _ (i : I) := UnramifiedSectionImmersion.isOpenImmersion f (a i) (ha i)
  let U : X.Opens := ⨆ i, (a i).opensRange
  have hp : IsProper (U.ι ≫ f) := union_isProper f a ha
  refine ⟨U, ProperNeighborhoodAtlas.projection_isFinite f ⟨U, hp⟩, inferInstance, ?_, ?_⟩
  · intro x hx
    exact (ProperNeighborhoodAtlas.mem_locus_iff f x).mpr ⟨U, hx, hp⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨i, y, hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      have hfy : f x = y := by
        rw [← hy, ← Scheme.Hom.comp_apply, ha]
        rfl
      exact ⟨i, hfy ▸ hy⟩
    · rintro ⟨i, hi⟩
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, f x, hi⟩

end FLT.Mazur.SectionProperNeighborhood
