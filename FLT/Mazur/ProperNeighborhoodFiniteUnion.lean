/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperEtaleNeighborhoodBases
public import FLT.Mazur.FiniteCoverUniversallyClosed

/-!
# One proper open containing a compact locus

Finite unions of actual proper open neighborhoods remain proper over a
separated locally finite type structural map. Compactness therefore constructs
one proper open containing the excluded locus. For etale maps this open is
finite over the unchanged ground, with no finite chart family supplied.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProperNeighborhoodAtlas
universe u v
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [IsSeparated f] [LocallyOfFiniteType f]
  {I : Type v} [Finite I] (U : I → X.Opens) [∀ i, IsProper ((U i).ι ≫ f)]

/-- A finite union of proper open neighborhoods remains proper over the same target. -/
theorem finiteUnion_isProper : IsProper ((iSup U).ι ≫ f) := by
  let g (i : I) : (U i).toScheme ⟶ (iSup U).toScheme := X.homOfLE (le_iSup U i)
  have hg : ∀ x : (iSup U).toScheme, ∃ i, ∃ z : (U i).toScheme, g i z = x := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.property
    refine ⟨i, ⟨x.val, hi⟩, ?_⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply _ _
  let _ (i : I) : UniversallyClosed (g i ≫ ((iSup U).ι ≫ f)) := by
    dsimp only [g]
    rw [Scheme.homOfLE_ι_assoc]
    infer_instance
  let _ := FiniteCoverUniversallyClosed.universallyClosed
    ((iSup U).ι ≫ f) (fun i ↦ (U i).toScheme) g hg
  exact ⟨⟩

omit [Finite I] in
/-- Compact subsets of the proper-neighborhood locus fit in one actual proper source open. -/
theorem exists_single_proper_open (K : Set X) (hK : IsCompact K) (h : K ⊆ locus f) :
    ∃ U : X.Opens, K ⊆ U ∧ IsProper (U.ι ≫ f) ∧ U ≤ locus f := by
  obtain ⟨J, hJ⟩ := exists_finite_cover f K hK h
  let U (i : J) : X.Opens := i.val.val
  let _ (i : J) : IsProper ((U i).ι ≫ f) := i.val.property
  have hp := finiteUnion_isProper f U
  refine ⟨iSup U, ?_, hp, ?_⟩
  · intro x hx
    obtain ⟨i, hi, z, rfl⟩ := hJ x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, z.property⟩
  · intro x hx
    exact (mem_locus_iff f x).mpr ⟨iSup U, hx, hp⟩

omit [LocallyOfFiniteType f] [Finite I] in
/-- For etale structural maps the constructed single neighborhood is genuinely finite. -/
theorem exists_single_finite_etale_open [Etale f]
    (K : Set X) (hK : IsCompact K) (h : K ⊆ locus f) :
    ∃ U : X.Opens, K ⊆ U ∧ Etale (U.ι ≫ f) ∧ IsFinite (U.ι ≫ f) ∧ U ≤ locus f := by
  obtain ⟨U, hKU, hp, hU⟩ := exists_single_proper_open f K hK h
  exact ⟨U, hKU, inferInstance, projection_isFinite f ⟨U, hp⟩, hU⟩

end FLT.Mazur.ProperNeighborhoodAtlas
