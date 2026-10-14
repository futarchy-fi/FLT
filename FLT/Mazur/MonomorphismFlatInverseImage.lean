/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonomorphismFppfImage
public import FLT.Mazur.MonomorphismPrincipalInverseCover
public import FLT.Mazur.SchemeFppfTargetOpen

/-!
# Constructing original inverse charts from flat comparison maps

For a finitely presented monomorphism, the full fppf target region is precisely
its inverse region. A flat comparison therefore gives original scheme inverses
around every image point. This includes all nilpotents in the target.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.MonomorphismOpenImage
variable {D K : Scheme.{u}} (m : D ⟶ K) [Mono m]

/-- Every point of an inverse chart is in the image of the original comparison. -/
theorem locus_subset_range : (locus m : Set K) ⊆ Set.range m := by
  intro x hx
  exact ⟨lift m ⟨x, hx⟩, congrArg (fun a ↦ a ⟨x, hx⟩) (lift_comp m)⟩

variable [LocallyOfFinitePresentation m]

/-- Flat surjective whole-source neighborhoods construct exactly the actual inverse locus. -/
theorem locus_eq_fppfTarget : locus m = SchemeFppfTargetOpen.locus m := by
  apply le_antisymm
  · apply (SchemeFppfTargetOpen.le_locus_iff m _).mpr
    let _ : IsIso (pullback.snd m (locus m).ι) := (inverseImageIso m).isIso_hom
    exact ⟨inferInstance, inferInstance⟩
  · intro x hx
    change x ∈ Set.range (SchemeFppfTargetOpen.map m) at hx
    apply fppf_image_le m (SchemeFppfTargetOpen.map m)
      (pullback.fst m (SchemeFlatTargetOpen.locus m).ι) _ hx
    exact pullback.condition

/-- If the original comparison is flat, every original image point has a scheme inverse. -/
theorem coe_locus_eq_range [Flat m] : (locus m : Set K) = Set.range m := by
  apply Set.Subset.antisymm (locus_subset_range m)
  exact fppf_image_le m m (𝟙 D) (Category.id_comp m)

/-- Flatness constructs finitely many actual principal inverses covering every original arrow. -/
theorem exists_principal_inverse_cover_range [Flat m] [IsAffine K] [NoetherianSpace K] :
    ∃ s : Finset Γ(K, ⊤),
      (∀ r ∈ s, ∃ a : (K.basicOpen r).toScheme ⟶ D, a ≫ m = (K.basicOpen r).ι) ∧
      ∀ x : K, x ∈ Set.range m ↔ ∃ r ∈ s, x ∈ K.basicOpen r := by
  obtain ⟨s, he, hs⟩ := exists_principal_inverse_cover m
  refine ⟨s, hs, fun x ↦ ?_⟩
  rw [← coe_locus_eq_range m]
  change x ∈ locus m ↔ _
  rw [← he, Opens.mem_iSup]
  exact ⟨fun ⟨r, hr⟩ ↦ ⟨r.val, r.property, hr⟩,
    fun ⟨r, hr, hx⟩ ↦ ⟨⟨r, hr⟩, hx⟩⟩

end FLT.Mazur.MonomorphismOpenImage
