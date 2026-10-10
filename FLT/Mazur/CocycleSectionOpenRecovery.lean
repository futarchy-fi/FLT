/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CocycleGlobalCoordinates
public import FLT.Mazur.CocycleGlobalSectionCoordinate
public import FLT.Mazur.OpenSectionTopComparison

/-!
# Recovering section opens from chart coordinates

Equality of the actual pulled-back chart functions recovers the complete
nonvanishing open of a global section, without selecting another section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.FCurve FLT.Mazur.Approximation

namespace FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle

universe u

variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (g : Cocycle U)

/-- Ambient global coordinates equal evaluation after restriction. -/
theorem globalCoordinate_eq_evaluate (s : g.sections ⊤) (i : ι)
    (V : Y.Opens) (h : V ≤ U i) :
    g.globalCoordinate s i V h = g.evaluate i h (g.restrict le_top s) := by
  exact (res_res _ _ _).symm

/-- The chart restriction of a generator open is the basic open of its global coordinate. -/
theorem sectionGeneratorOpen_coordinate (hU : iSup U = ⊤) (s : g.sections ⊤)
    (i : ι) (V : Y.Opens) (h : V ≤ U i) :
    V.ι ⁻¹ᵁ sectionGeneratorOpen g.sheaf s =
      V.toScheme.basicOpen (V.topIso.inv (g.globalCoordinate s i V h)) := by
  rw [globalCoordinate_eq_evaluate]
  exact g.sectionGeneratorOpen_preimage hU i V h s

/-- Exact chart-coordinate pullback recovers the whole nonvanishing open. -/
theorem sectionGeneratorOpen_eq_preimage_of_coordinates (hU : iSup U = ⊤)
    (f : X ⟶ Y) (s : g.sections ⊤) (t : (g.inverseImage f).sections ⊤)
    (h : ∀ i, f.app (U i) (g.globalCoordinate s i (U i) le_rfl) =
      (g.inverseImage f).globalCoordinate t i (f ⁻¹ᵁ U i) le_rfl) :
    sectionGeneratorOpen (g.inverseImage f).sheaf t = f ⁻¹ᵁ sectionGeneratorOpen g.sheaf s := by
  have he (i : ι) : (f ⁻¹ᵁ U i).ι ⁻¹ᵁ sectionGeneratorOpen (g.inverseImage f).sheaf t =
      (f ⁻¹ᵁ U i).ι ⁻¹ᵁ (f ⁻¹ᵁ sectionGeneratorOpen g.sheaf s) := by
    rw [(g.inverseImage f).sectionGeneratorOpen_coordinate (inverseImage_cover f hU)
        t i (f ⁻¹ᵁ U i) le_rfl,
      ← Scheme.Hom.comp_preimage, ← morphismRestrict_ι, Scheme.Hom.comp_preimage,
      g.sectionGeneratorOpen_coordinate hU s i (U i) le_rfl, Scheme.preimage_basicOpen_top]
    congr 1
    apply (ConcreteCategory.bijective_of_isIso (f ⁻¹ᵁ U i).topIso.hom).injective
    rw [Iso.inv_hom_id_apply, ← Scheme.Hom.resLE_eq_morphismRestrict, ← topIso_hom_resLE,
      Iso.inv_hom_id_apply]
    simpa only [Scheme.Hom.app_eq_appLE] using (h i).symm
  apply Opens.ext
  apply Set.ext
  intro x
  obtain ⟨i, hi⟩ : ∃ i, x ∈ f ⁻¹ᵁ U i := Opens.mem_iSup.mp (by
    rw [inverseImage_cover f hU]
    trivial)
  exact Iff.of_eq (congrArg (fun V : (f ⁻¹ᵁ U i).toScheme.Opens ↦
    (⟨x, hi⟩ : (f ⁻¹ᵁ U i).toScheme) ∈ V) (he i))

end FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle
