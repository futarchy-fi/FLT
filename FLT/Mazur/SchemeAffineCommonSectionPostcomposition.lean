/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineExplicitCommonSectionMaps
public import FLT.Mazur.SchemeAffineNamedSectionPostcomposition

/-!
# Common-section cancellation preserving transport

Cancel the constructed common section even when a morphism follows the left
reconstruction and its original source map differs from the right source map.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeAffineDescent.Chart
open SheafPullbackPathComparison SchemeModulePullbackUnits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} {p : Y ⟶ X} (C : Chart p)
variable {M : Y.Modules} (D : SchemeGeometricDescent.Data p M)
variable [((pullback C.cover).obj M).IsQuasicoherent]
attribute [local irreducible] sheaf refinementReconstruction reconstruction

variable (C' : Chart p)
variable {A : CommRingCat.{u}} (f : C.baseRing ⟶ A) (g : C'.baseRing ⟶ A)
variable (w : Spec.map f ≫ C.base = Spec.map g ≫ C'.base)

variable [((pullback C'.cover).obj M).IsQuasicoherent]

/-- Cancel a common-cover section while preserving a morphism between the targets. -/
lemma commonSectionOriginalMap_postcomp
    (s : Spec A ⟶ Spec (C.commonCoverRing C' f g))
    (hs : s ≫ Spec.map (C.commonCoverMap C' f g) = 𝟙 (Spec A))
    (t : Spec A ⟶ Spec C.coverRing) (ht : s ≫ Spec.map (C.commonCoverLeft C' f g) = t)
    (ha : t ≫ Spec.map C.ringMap = Spec.map f)
    (v : Spec A ⟶ Spec C'.coverRing) (hv : s ≫ Spec.map (C.commonCoverRight C' f g) = v)
    (hg : v ≫ Spec.map C'.ringMap = Spec.map g)
    (d : Spec A ⟶ Y)
    (hd : s ≫ (C.commonBaseCrossRefinement C' f g w).leftChart.cover = d)
    (d' : Spec A ⟶ Y)
    (hd' : s ≫ (C.commonBaseCrossRefinement C' f g w).rightChart.cover = d')
    (hcd : t ≫ C.cover = d) (hcd' : v ≫ C'.cover = d')
    (k : (pullback d).obj M ⟶ (pullback d').obj M)
    {B : (Spec A).Modules}
    (e : B ⟶ (pullback (Spec.map f)).obj (C.sheaf D))
    (e' : B ⟶ (pullback (Spec.map g)).obj (C'.sheaf D))
    (h : C.commonSectionLeftMap D C' f g w s d hd e ≫ k =
      C.commonSectionRightMap D C' f g w s d' hd' e') :
    C.sectionOriginalMap D f t ha d hcd e ≫ k =
      C'.sectionOriginalMap D g v hg d' hcd' e' := by
  suffices hh : CrossRefinement.sectionPostcompose
      (C.sectionOriginalMap D f t ha d hcd e) k =
        C'.sectionOriginalMap D g v hg d' hcd' e' by
    simpa only [CrossRefinement.sectionPostcompose] using hh
  apply CrossRefinement.sectionOriginalMap_postcomp_mk D A
    (C.commonCoverRing C' f g) (C.commonCoverMap C' f g)
    (C.commonCoverMap_faithfullyFlat C' f g) f g
    (C.commonCoverLeft C' f g) (C.commonCoverRight C' f g)
    (C.commonCoverLeft_square C' f g) (C.commonCoverRight_square C' f g) w
    s hs t ht ha v hv hg d hd d' hd' hcd hcd' k e e'
  have hh : CrossRefinement.sectionPostcompose
      (C.commonSectionLeftMap D C' f g w s d hd e) k =
        C.commonSectionRightMap D C' f g w s d' hd' e' := by
    simpa only [CrossRefinement.sectionPostcompose] using h
  unfold commonSectionLeftMap commonSectionRightMap at hh
  exact (congrArg (CrossRefinement.sectionPostcompose · k)
    (commonSectionLeftMap_eq C D C' f g w s d hd e)).trans
      (hh.trans (commonSectionRightMap_eq C D C' f g w s d' hd' e').symm)

end FLT.Mazur.SchemeAffineDescent.Chart
