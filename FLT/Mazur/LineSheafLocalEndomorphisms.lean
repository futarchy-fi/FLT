/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafScalarEndomorphisms
public import FLT.Mazur.ModuleSheafOpenImmersionLocalHom
public import FLT.Mazur.DivisorInvertibleSheaf

/-!
# Endomorphisms on a trivializing open

A scheme-level rank-one chart gives a slice-site trivialization. Conjugation
by this trivialization identifies local endomorphisms with scalar multiplication.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.ModuleSheafScalarEndomorphisms
open ModuleSheafInternalHom
variable {X : Scheme.{u}} {M N : X.Modules}

/-- An actual scheme restriction trivialization also trivializes the slice module. -/
def sliceTrivialization (U : X.Opens) (e : M.restrict U.ι ≅ structureModule U.toScheme) :
    M.over U ≅ (structureModule X).over U := by
  let e' := e ≪≫ (restrictUnitIso U.ι).symm
  let a := ModuleSheafOpenImmersionLocalHom.ofRestriction U.ι e'.hom
  have : IsIso a := by
    dsimp [a, ModuleSheafOpenImmersionLocalHom.ofRestriction]
    infer_instance
  have hU : U.ι.opensRange = U := Scheme.Opens.opensRange_ι U
  exact hU ▸ (asIso a : M.over U.ι.opensRange ≅
    (structureModule X).over U.ι.opensRange)

/-- Changing local frames leaves scalar multiplication unchanged. -/
lemma conjugate_scalar {U : X.Opens} (e : M.over U ≅ N.over U) (r : Γ(X, U)) :
    e.inv ≫ (scalarMap M).app U r ≫ e.hom = (scalarMap N).app U r := by
  apply sections_ext
  intro V s
  have he := congrArg (fun k ↦ app N N k V s) e.inv_hom_id
  change (e.hom.val.app (op V)).hom ((e.inv.val.app (op V)).hom s) = s at he
  change (e.hom.val.app (op V)).hom
    (X.presheaf.map V.hom.op r • (e.inv.val.app (op V)).hom s) =
      X.presheaf.map V.hom.op r • s
  rw [LinearMap.map_smul, he]

/-- Scalars classify endomorphisms on any trivializing slice. -/
lemma bijective_of_slice {U : X.Opens} (e : M.over U ≅ (structureModule X).over U) :
    Function.Bijective ((scalarMap M).app U) := by
  constructor
  · intro r s h
    apply (unit_bijective U).injective
    rw [← conjugate_scalar e r, ← conjugate_scalar e s, h]
  · intro φ
    obtain ⟨r, hr⟩ := (unit_bijective U).surjective (e.inv ≫ φ ≫ e.hom)
    refine ⟨r, ?_⟩
    apply (cancel_epi e.inv).mp
    apply (cancel_mono e.hom).mp
    simpa only [Category.assoc, conjugate_scalar] using hr

/-- On a rank-one chart the actual internal scalar map is bijective on sections. -/
lemma bijective_of_trivialization (U : X.Opens)
    (e : M.restrict U.ι ≅ structureModule U.toScheme) :
    Function.Bijective ((scalarMap M).app U) :=
  bijective_of_slice (sliceTrivialization U e)

end FLT.Mazur.FCurve.ModuleSheafScalarEndomorphisms
