/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossSectionMaps

/-!
# Cancellation in independently named ring coordinates

The cross-refinement cancellation is expressed with independently named
base and covering rings. This isolates projection conversion before applying
the result to constructed pushout rings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
open SheafPullbackPathComparison SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} {C C' : Chart p}
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
variable [((pullback C'.cover).obj M).IsQuasicoherent]
variable (A T : CommRingCat.{u}) (φ : A ⟶ T) (hφ : φ.hom.FaithfullyFlat)
variable (f : C.baseRing ⟶ A) (g : C'.baseRing ⟶ A)
variable (b : C.coverRing ⟶ T) (c : C'.coverRing ⟶ T)
variable (hb : C.ringMap ≫ b = f ≫ φ) (hc : C'.ringMap ≫ c = g ≫ φ)
variable (w : Spec.map f ≫ C.base = Spec.map g ≫ C'.base)
attribute [local irreducible] Chart.sheaf Chart.refinementReconstruction Chart.reconstruction

/-- Common-section cancellation retains explicit base and covering ring coordinates. -/
lemma sectionOriginalMap_eq_mk
    (s : Spec A ⟶ Spec T)
    (hs : s ≫ Spec.map φ = 𝟙 (Spec A))
    (t : Spec A ⟶ Spec C.coverRing) (ht : s ≫ Spec.map b = t)
    (ha : t ≫ Spec.map C.ringMap = Spec.map f)
    (v : Spec A ⟶ Spec C'.coverRing) (hv : s ≫ Spec.map c = v)
    (hg : v ≫ Spec.map C'.ringMap = Spec.map g)
    (d : Spec A ⟶ Y) (hd : s ≫ (Spec.map b ≫ C.cover) = d)
    (hd' : s ≫ (Spec.map c ≫ C'.cover) = d) (hcd : t ≫ C.cover = d) (hcd' : v ≫ C'.cover = d)
    {B : (Spec A).Modules}
    (e : B ⟶ (pullback (Spec.map f)).obj (C.sheaf D))
    (e' : B ⟶ (pullback (Spec.map g)).obj (C'.sheaf D))
    (h : let ρ : C.CrossRefinement C' := ⟨A, T, φ, hφ, f, g, b, c, hb, hc, w⟩
      ρ.sectionLeftMap D s d hd e = ρ.sectionRightMap D s d hd' e') :
    C.sectionOriginalMap D f t ha d hcd e = C'.sectionOriginalMap D g v hg d hcd' e' := by
  exact sectionOriginalMap_eq D
    (⟨A, T, φ, hφ, f, g, b, c, hb, hc, w⟩ : C.CrossRefinement C')
    s hs t ht ha v hv hg d hd hd' hcd hcd' (B := B) e e' h

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
