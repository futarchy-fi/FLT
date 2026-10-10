/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CocycleSectionOpenRecovery

/-!
# Comparing section opens across compositional chart identifications

Only the recovered chart coordinates are needed to identify generator opens.
The two cocycles need not be definitionally the same inverse-image cocycle.
This allows cone composition to identify the original and stage section opens.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open FLT.Mazur.FCurve FLT.Mazur.Approximation

namespace FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle

universe u

variable {X Y Z : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens} (g : Cocycle U)

/-- Matching coordinates on inverse-image charts identify complete generator opens. -/
theorem sectionGeneratorOpen_eq_preimage_of_chart_comparison (hU : iSup U = ⊤)
    (f : X ⟶ Y) (a : Cocycle (fun i ↦ f ⁻¹ᵁ U i))
    (s : g.sections ⊤) (t : a.sections ⊤)
    (h : ∀ i, f.app (U i) (g.globalCoordinate s i (U i) le_rfl) =
      a.globalCoordinate t i (f ⁻¹ᵁ U i) le_rfl) :
    sectionGeneratorOpen a.sheaf t = f ⁻¹ᵁ sectionGeneratorOpen g.sheaf s := by
  have he (i : ι) : (f ⁻¹ᵁ U i).ι ⁻¹ᵁ sectionGeneratorOpen a.sheaf t =
      (f ⁻¹ᵁ U i).ι ⁻¹ᵁ (f ⁻¹ᵁ sectionGeneratorOpen g.sheaf s) := by
    rw [a.sectionGeneratorOpen_coordinate (inverseImage_cover f hU)
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

/-- Cone composition and ambient coordinate recovery identify the two section opens. -/
theorem inverseImage_sectionGeneratorOpen_composition {V : ι → Z.Opens}
    (b : Cocycle V) (hV : iSup V = ⊤) (f : Y ⟶ Z) (q : X ⟶ Y) (p : X ⟶ Z)
    (hp : q ≫ f = p) (s : (b.inverseImage f).sections ⊤)
    (t : (b.inverseImage p).sections ⊤)
    (h : ∀ i, q.appLE (f ⁻¹ᵁ V i) (p ⁻¹ᵁ V i)
        (by rw [← hp, Scheme.Hom.comp_preimage])
        ((b.inverseImage f).globalCoordinate s i (f ⁻¹ᵁ V i) le_rfl) =
      (b.inverseImage p).globalCoordinate t i (p ⁻¹ᵁ V i) le_rfl) :
    sectionGeneratorOpen (b.inverseImage p).sheaf t =
      q ⁻¹ᵁ sectionGeneratorOpen (b.inverseImage f).sheaf s := by
  subst p
  apply (b.inverseImage f).sectionGeneratorOpen_eq_preimage_of_chart_comparison
    (inverseImage_cover f hV) q (b.inverseImage (q ≫ f)) s t
  intro i
  simpa only [Scheme.Hom.comp_preimage, Scheme.Hom.app_eq_appLE] using h i

end FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle
