/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealModulePrincipalPullback
public import FLT.Mazur.ModuleSheafOpenIsoDetection

/-!
# Canonical ideal-module comparison for relative Cartier base change

Affine Cartier charts prove invertibility without assuming a flat base map.
Restriction compatibility then identifies these local maps with the actual
canonical comparison on the whole pullback scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X S T : Scheme.{u}}

/-- A scheme open cover detects invertibility of a morphism of module sheaves. -/
lemma moduleHom_isIso_of_schemeOpenCover {M N : X.Modules} (a : M ⟶ N)
    (C : X.OpenCover) (h : ∀ i, IsIso ((restrictFunctor (C.f i)).map a)) : IsIso a := by
  apply ModuleSheafOpenIsoDetection.isIso_of_iSup_eq_top a
    (fun i ↦ (C.f i).opensRange) C.iSup_opensRange
  intro i
  let := h i
  exact moduleHom_isIso_restrict_opensRange a (C.f i)

/-- The canonical comparison is invertible over an affine base. -/
theorem relativeCartierIdealPullback_affineBase [IsAffine S]
    (f : X ⟶ S) (g : T ⟶ S) (I : X.IdealSheafData)
    (hI : RelativeEffectiveCartier f I) :
    IsIso (idealModulePullbackHom I (pullback.fst f g)) := by
  classical
  let := hI.2
  choose U hx hU using hI.1
  let C := X.openCoverOfIsOpenCover (fun x ↦ (U x).1) (by
    change (⨆ x, (U x).1) = ⊤
    ext x
    exact ⟨fun _ ↦ trivial, fun _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩⟩)
  apply moduleHom_isIso_of_schemeOpenCover _
    (Scheme.Pullback.openCoverOfLeftRight C T.affineCover f g)
  rintro ⟨x, j⟩
  have : IsAffine (C.X x) := (U x).2
  have : Flat ((I.comap (C.f x)).subschemeι ≫ C.f x ≫ f) :=
    flat_comap_of_flat f (C.f x) I
  have hc : CartierChart (I.comap (C.f x)) ⟨⊤, isAffineOpen_top (C.X x)⟩ :=
    CartierChart.comap_ι_top (hU x)
  have := idealModulePullbackHom_isIso_affine_relative
    (C.f x ≫ f) (T.affineCover.f j ≫ g) (I.comap (C.f x)) hc
  apply idealModulePullbackHom_isIso_restrict I (pullback.fst f g)
    (pullback.fst (C.f x ≫ f) (T.affineCover.f j ≫ g)) _ (C.f x)
  simp [Scheme.Pullback.openCoverOfLeftRight_f]

/-- Arbitrary relative Cartier base change identifies the actual ideal modules. -/
theorem relativeCartierIdealPullback (f : X ⟶ S) (g : T ⟶ S)
    (I : X.IdealSheafData) (hI : RelativeEffectiveCartier f I) :
    IsIso (idealModulePullbackHom I (pullback.fst f g)) := by
  apply moduleHom_isIso_of_schemeOpenCover _
    (Scheme.Pullback.openCoverOfBase S.affineCover f g)
  intro i
  have hi : RelativeEffectiveCartier (pullback.snd f (S.affineCover.f i))
      (I.comap (pullback.fst f (S.affineCover.f i))) :=
    ⟨hI.1.comap_of_isOpenImmersion _, hI.flat_baseChange _⟩
  have := relativeCartierIdealPullback_affineBase
    (pullback.snd f (S.affineCover.f i)) (pullback.snd g (S.affineCover.f i))
    (I.comap (pullback.fst f (S.affineCover.f i))) hi
  apply idealModulePullbackHom_isIso_restrict I (pullback.fst f g)
    (pullback.fst (pullback.snd f (S.affineCover.f i))
      (pullback.snd g (S.affineCover.f i))) _ (pullback.fst f (S.affineCover.f i))
  simp [Scheme.Pullback.openCoverOfBase_f]

end FLT.Mazur.FCurve
