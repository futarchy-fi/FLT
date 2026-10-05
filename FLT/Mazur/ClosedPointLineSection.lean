/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteClosedIdealSection
public import FLT.Mazur.AffineTrivialLineSectionOpen

/-!
# Sections generating at a closed point over any base

An invertible sheaf on a one-point scheme is trivial: any trivializing open
is the whole scheme. The comaximal ideal sequence then lifts a generator
without assuming that the ambient scheme is over a field.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules

namespace FLT.Mazur.FCurve
open ModuleSheafTensor CoherentIdealIntersection FLT.Mazur.GlobalIdealPower

/-- On a one-point scheme every line sheaf has a global trivialization. -/
theorem LocallyFreeRankOne.trivial_of_subsingleton {X : Scheme} [Subsingleton X]
    {L : X.Modules} (hL : LocallyFreeRankOne L) (x : X) :
    Nonempty (L ≅ structureModule X) := by
  obtain ⟨U, hx, _, ⟨e⟩⟩ := hL.exists_affine_trivialization x
  have hU : U = ⊤ := by
    apply top_unique
    intro y _
    exact Subsingleton.elim x y ▸ hx
  subst U
  exact ⟨(restrictFunctorId.app L).symm ≪≫
    (restrictFunctorCongr X.toIso_inv_ι.symm).app L ≪≫
    (restrictFunctorComp X.topIso.inv (⊤ : X.Opens).ι).app L ≪≫
    (restrictFunctor X.topIso.inv).mapIso e ≪≫ restrictUnitIso X.topIso.inv⟩

/-- A trivialization on a closed subscheme suffices to lift an ideal section generating there. -/
theorem exists_ideal_section_generating_trivial_closed {X : Scheme}
    (I J : X.IdealSheafData) (hIJ : I ⊔ J = ⊤) {L : X.Modules}
    (hL : LocallyFreeRankOne L)
    (e : (pullback J.subschemeι).obj L ≅ structureModule J.subscheme)
    [Subsingleton (ModuleH (tensor (idealModule (I ⊓ J)) L) 1)] :
    ∃ t : Γ(tensor (idealModule I) L, ⊤),
      (J.support : Set X) ⊆ sectionGeneratorOpen L ((scalarAction I L).app ⊤ t) := by
  let i := J.subschemeι
  let P := (pullback i).obj L
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
