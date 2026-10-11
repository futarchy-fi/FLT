/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Naturality with explicitly identified section domains

Equality transports commute with restrictions. This keeps comparison proofs in
structure-sheaf coordinates without unfolding the constructions of their rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u v
namespace FLT.Mazur.SchemeEffectiveEpiSections

/-- Equality transports of section domains commute with every restriction. -/
theorem sectionTransport_naturality {T : TopCat.{u}}
    (F : T.Presheaf CommRingCat.{v})
    {U U' W W' : TopologicalSpace.Opens T} (eU : U = U') (eW : W = W')
    (h : W ≤ U) (h' : W' ≤ U') (s : F.obj (op U)) :
    F.map (eqToHom (congrArg op eW)) (F.map (homOfLE h).op s) =
      F.map (homOfLE h').op (F.map (eqToHom (congrArg op eU)) s) := by
  subst U'
  subst W'
  simp only [eqToHom_refl, F.map_id, CommRingCat.id_apply]

/-- Pullback of regular functions commutes with restriction on both schemes. -/
theorem sectionPullback_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U W : Y.Opens} (h : W ≤ U) (s : Γ(Y, U)) :
    f.app W (Y.presheaf.map (homOfLE h).op s) =
      X.presheaf.map ((TopologicalSpace.Opens.map f.base).map (homOfLE h)).op
        (f.app U s) :=
  congrArg (fun k ↦ k s) (f.naturality (homOfLE h).op)

/-- A natural transformation of ring presheaves preserves every section restriction. -/
theorem sectionTransformation_naturality {T : TopCat.{u}}
    {F G : T.Presheaf CommRingCat.{v}} (η : F ⟶ G)
    {U W : TopologicalSpace.Opens T} (h : W ≤ U) (s : F.obj (op U)) :
    η.app (op W) (F.map (homOfLE h).op s) =
      G.map (homOfLE h).op (η.app (op U) s) :=
  congrArg (fun k ↦ k s) (η.naturality (homOfLE h).op)

end FLT.Mazur.SchemeEffectiveEpiSections
