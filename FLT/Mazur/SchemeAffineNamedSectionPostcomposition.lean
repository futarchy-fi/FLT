/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineCrossSectionPostcomposition

/-!
# Section cancellation with a morphism between distinct targets

Named base and covering rings isolate conversion when applying section
cancellation to transport between different original source maps.
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

/-- Sealed postcomposition keeps projected scheme categories out of conversion. -/
def sectionPostcompose {A : CommRingCat.{u}} {B P Q : (Spec A).Modules}
    (a : B ⟶ P) (k : P ⟶ Q) : B ⟶ Q := a ≫ k

attribute [irreducible] sectionPostcompose

variable (ρ : C.CrossRefinement C')

/-- Cancel a common section between sealed maps with distinct target pullbacks. -/
lemma sectionOriginalMap_postcomp
    (s : Spec ρ.baseRing ⟶ Spec ρ.coverRing)
    (hs : s ≫ Spec.map ρ.ringMap = 𝟙 (Spec ρ.baseRing))
    (t : Spec ρ.baseRing ⟶ Spec C.coverRing) (ht : s ≫ Spec.map ρ.leftCover = t)
    (ha : t ≫ Spec.map C.ringMap = Spec.map ρ.leftBase)
    (v : Spec ρ.baseRing ⟶ Spec C'.coverRing) (hv : s ≫ Spec.map ρ.rightCover = v)
    (hb : v ≫ Spec.map C'.ringMap = Spec.map ρ.rightBase)
    (d : Spec ρ.baseRing ⟶ Y) (hd : s ≫ ρ.leftChart.cover = d)
    (d' : Spec ρ.baseRing ⟶ Y) (hd' : s ≫ ρ.rightChart.cover = d')
    (hcd : t ≫ C.cover = d) (hcd' : v ≫ C'.cover = d')
    (k : (pullback d).obj M ⟶ (pullback d').obj M)
    {B : (Spec ρ.baseRing).Modules}
    (e : B ⟶ (pullback (Spec.map ρ.leftBase)).obj (C.sheaf D))
    (e' : B ⟶ (pullback (Spec.map ρ.rightBase)).obj (C'.sheaf D))
    (h : sectionPostcompose (ρ.sectionLeftMap D s d hd e) k = ρ.sectionRightMap D s d' hd' e') :
    sectionPostcompose (C.sectionOriginalMap D ρ.leftBase t ha d hcd e) k =
      C'.sectionOriginalMap D ρ.rightBase v hb d' hcd' e' := by
  unfold sectionPostcompose sectionLeftMap sectionRightMap at h
  unfold sectionPostcompose Chart.sectionOriginalMap
  simpa only [Category.assoc] using
    section_comparison_postcomp D ρ s hs t ht ha v hv hb d hd d' hd' hcd hcd' k e e'
      (by simpa only [Category.assoc] using h)

/-- Section cancellation preserves postcomposition in explicitly named ring coordinates. -/
lemma sectionOriginalMap_postcomp_mk
    (s : Spec A ⟶ Spec T)
    (hs : s ≫ Spec.map φ = 𝟙 (Spec A))
    (t : Spec A ⟶ Spec C.coverRing) (ht : s ≫ Spec.map b = t)
    (ha : t ≫ Spec.map C.ringMap = Spec.map f)
    (v : Spec A ⟶ Spec C'.coverRing) (hv : s ≫ Spec.map c = v)
    (hg : v ≫ Spec.map C'.ringMap = Spec.map g)
    (d : Spec A ⟶ Y) (hd : s ≫ (Spec.map b ≫ C.cover) = d)
    (d' : Spec A ⟶ Y) (hd' : s ≫ (Spec.map c ≫ C'.cover) = d')
    (hcd : t ≫ C.cover = d) (hcd' : v ≫ C'.cover = d')
    (k : (pullback d).obj M ⟶ (pullback d').obj M)
    {B : (Spec A).Modules}
    (e : B ⟶ (pullback (Spec.map f)).obj (C.sheaf D))
    (e' : B ⟶ (pullback (Spec.map g)).obj (C'.sheaf D))
    (h : let ρ : C.CrossRefinement C' := ⟨A, T, φ, hφ, f, g, b, c, hb, hc, w⟩
      sectionPostcompose (ρ.sectionLeftMap D s d hd e) k = ρ.sectionRightMap D s d' hd' e') :
    sectionPostcompose (C.sectionOriginalMap D f t ha d hcd e) k =
      C'.sectionOriginalMap D g v hg d' hcd' e' := by
  exact sectionOriginalMap_postcomp D
    (⟨A, T, φ, hφ, f, g, b, c, hb, hc, w⟩ : C.CrossRefinement C')
    s hs t ht ha v hv hg d hd d' hd' hcd hcd' k (B := B) e e' h

end FLT.Mazur.SchemeAffineDescent.Chart.CrossRefinement
