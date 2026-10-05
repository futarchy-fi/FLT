/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealQuotientSectionLift
public import FLT.Mazur.IdealTwistSectionOpen
public import FLT.Mazur.LineStructureProjection
public import FLT.Mazur.FiniteSchemeLineTwist
public import FLT.Mazur.LineBundleSectionOpenPullback

/-!
# Ideal sections generating along a finite closed subscheme

A line on a finite scheme over a field is trivial. Lift its unit section
through the comaximal ideal sequence using H¹ vanishing. The projection
formula identifies its image with actual pullback, so the lifted section
generates at every point of the finite closed subscheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

open ModuleSheafTensor CoherentIdealIntersection FLT.Mazur.GlobalIdealPower

variable {k : Type} [Field k] {X : Scheme}

/-- Projected ideal reduction is the pullback unit applied to scalar multiplication. -/
lemma idealReduction_projection (I J : X.IdealSheafData) {L : X.Modules}
    (hL : LocallyFreeRankOne L) :
    ModuleSheafTensor.map (reduction I J) (𝟙 L) ≫
        (LineStructureProjection.iso J.subschemeι L hL).hom =
      scalarAction I L ≫ (pullbackPushforwardAdjunction J.subschemeι).unit.app L := by
  apply ModuleSheafTensor.hom_ext
  intro U a l
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, map_pure, Hom.id_app,
    ConcreteCategory.id_apply, scalarAction_pure]
  erw [LineStructureProjection.iso_pure]
  exact (((pullbackPushforwardAdjunction J.subschemeι).unit.app L).val.app
    (op U)).hom.map_smul ((idealModuleι I).app U a) l |>.symm

/-- The unit in any trivialization generates the line everywhere. -/
lemma trivialLine_unit_generatorOpen {Y : Scheme} {M : Y.Modules}
    (e : M ≅ structureModule Y) :
    sectionGeneratorOpen M (e.inv.app ⊤ (1 : Γ(Y, ⊤))) = ⊤ := by
  rw [← sectionGeneratorOpen_iso e]
  have he : e.hom.app ⊤ (e.inv.app ⊤ (1 : Γ(Y, ⊤))) = (1 : Γ(Y, ⊤)) := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.inv_hom_id]
    rfl
  rw [he, sectionGeneratorOpen_structure, Y.basicOpen_one]

/-- H¹ vanishing constructs an ideal-multiple section generating on the finite closed locus. -/
theorem exists_ideal_section_generating_finite (f : X ⟶ Spec (CommRingCat.of k))
    (I J : X.IdealSheafData) (hIJ : I ⊔ J = ⊤) [IsFinite (J.subschemeι ≫ f)]
    {L : X.Modules} (hL : LocallyFreeRankOne L)
    [Subsingleton (ModuleH (tensor (idealModule (I ⊓ J)) L) 1)] :
    ∃ t : Γ(tensor (idealModule I) L, ⊤),
      (J.support : Set X) ⊆ sectionGeneratorOpen L ((scalarAction I L).app ⊤ t) := by
  let i := J.subschemeι
  let P := (pullback i).obj L
  let e : P ≅ structureModule J.subscheme := finiteSchemeLineIso (i ≫ f) (hL.pullback i)
  let v : Γ(P, ⊤) := e.inv.app ⊤ (1 : Γ(J.subscheme, ⊤))
  let ep := LineStructureProjection.iso i L hL
  let w : Γ((pushforward i).obj P, ⊤) := v
  obtain ⟨t, ht⟩ := comaximalLineReduction_surjective I J hIJ hL (ep.inv.app ⊤ w)
  let s := (scalarAction I L).app ⊤ t
  have hu : ((pullbackPushforwardAdjunction i).unit.app L).app ⊤ s = w := by
    have h := congrArg (fun a ↦ ep.hom.app ⊤ a) ht
    have he : ep.hom.app ⊤ (ep.inv.app ⊤ w) = w :=
      ConcreteCategory.congr_hom (congrArg (fun a ↦ a.app ⊤) ep.inv_hom_id) w
    rw [he] at h
    exact (congrArg (fun a ↦ a.app ⊤ t) (idealReduction_projection I J hL)).symm.trans h
  have hv : pullGlobal i L s = v := hu
  have hg : sectionGeneratorOpen P v = ⊤ := trivialLine_unit_generatorOpen e
  refine ⟨t, ?_⟩
  intro x hx
  obtain ⟨z, rfl⟩ := J.range_subschemeι.symm ▸ hx
  have hz : z ∈ sectionGeneratorOpen P (pullGlobal i L s) := by rw [hv, hg]; trivial
  rw [sectionGeneratorOpen_pullGlobal hL] at hz
  exact hz

end FLT.Mazur.FCurve
