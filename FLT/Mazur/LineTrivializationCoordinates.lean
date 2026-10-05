/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteAffineLineCover
public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Ambient coordinates from a line trivialization

A genuine trivialization on an open subscheme gives linear coordinates on
every ambient subopen. Both directions commute with restriction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.ModuleSheafMorphismGluing

namespace FLT.Mazur.FCurve

universe u

variable {X : Scheme.{u}} {L : X.Modules} {U : X.Opens}

/-- Lift a geometric line trivialization to the slice site. -/
def lineTrivializationSlice (e : L.restrict U.ι ≅ structureModule U.toScheme) :
    L.over U ≅ (structureModule X).over U :=
  (overEquiv U).fullyFaithfulFunctor.preimageIso
    ((overFunctorEquiv U).app L ≪≫ e ≪≫ (restrictUnitIso U.ι).symm ≪≫
      ((overFunctorEquiv U).app (structureModule X)).symm)

/-- Coordinates of sections on any ambient subopen of a trivializing chart. -/
def lineTrivializationCoordinates (e : L.restrict U.ι ≅ structureModule U.toScheme)
    {V : X.Opens} (h : V ≤ U) : Γ(L, V) ≃ₗ[Γ(X, V)] Γ(X, V) where
  toLinearMap := localApp (lineTrivializationSlice e).hom h
  invFun := localApp (lineTrivializationSlice e).inv h
  left_inv s := by
    have hh := congrArg (fun a : L.over U ⟶ L.over U ↦ localApp a h s)
      (lineTrivializationSlice e).hom_inv_id
    exact hh
  right_inv s := by
    have hh := congrArg (fun a : (structureModule X).over U ⟶ (structureModule X).over U ↦
      localApp a h s) (lineTrivializationSlice e).inv_hom_id
    exact hh

/-- Coordinate maps commute with ambient restriction. -/
theorem lineTrivializationCoordinates_restrict
    (e : L.restrict U.ι ≅ structureModule U.toScheme)
    {V W : X.Opens} (h : W ≤ V) (hV : V ≤ U) (s : Γ(L, V)) :
    lineTrivializationCoordinates e (h.trans hV) (res L h s) =
      X.presheaf.map (homOfLE h).op (lineTrivializationCoordinates e hV s) :=
  localApp_res (lineTrivializationSlice e).hom h hV s

/-- Inverse coordinate maps also commute with ambient restriction. -/
theorem lineTrivializationCoordinates_symm_restrict
    (e : L.restrict U.ι ≅ structureModule U.toScheme)
    {V W : X.Opens} (h : W ≤ V) (hV : V ≤ U) (s : Γ(X, V)) :
    (lineTrivializationCoordinates e (h.trans hV)).symm
        (X.presheaf.map (homOfLE h).op s) =
      res L h ((lineTrivializationCoordinates e hV).symm s) :=
  localApp_res (lineTrivializationSlice e).inv h hV s

end FLT.Mazur.FCurve
