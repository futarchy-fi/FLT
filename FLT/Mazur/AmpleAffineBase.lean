/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffinePullback

/-!
# Section ampleness over an affine base

Restriction along affine open immersions preserves ampleness. Over an affine
base, relative section ampleness is exactly absolute section ampleness, provided
the structural morphism is quasi-compact.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
variable {X Y S : Scheme.{u}} {L : X.Modules}

/-- Affine open restriction preserves the affine-section-open ample predicate. -/
theorem AmpleLineBundle.restrict_affine (hL : AmpleLineBundle L)
    (j : Y ⟶ X) [IsOpenImmersion j] [IsAffineHom j] :
    AmpleLineBundle (L.restrict j) :=
  (hL.pullback_affine j).of_iso ((restrictFunctorIsoPullback j).app L)

/-- Restriction along an isomorphism reflects as well as preserves ampleness. -/
theorem ampleLineBundle_restrict_iso_iff (j : Y ⟶ X) [IsIso j] :
    AmpleLineBundle (L.restrict j) ↔ AmpleLineBundle L := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.restrict_affine j⟩
  exact (h.restrict_affine (inv j)).of_iso
    ((restrictFunctorId.app L).symm ≪≫
      (restrictFunctorCongr (IsIso.inv_hom_id j).symm).app L ≪≫
      (restrictFunctorComp (inv j) j).app L)

/-- Over an affine base, relative section ampleness implies absolute ampleness. -/
theorem RelativelyAmpleLineBundle.ample_of_affine {f : X ⟶ S} [IsAffine S]
    (hL : RelativelyAmpleLineBundle f L) : AmpleLineBundle L := by
  have h := hL.2.2 ⊤ (isAffineOpen_top S)
  simp only [Scheme.Hom.preimage_top] at h
  exact (ampleLineBundle_restrict_iso_iff X.topIso.hom).mp h

/-- Absolute ampleness is relative ampleness over an affine base. -/
theorem AmpleLineBundle.relative_of_affine (hL : AmpleLineBundle L)
    (f : X ⟶ S) [IsAffine S] [QuasiCompact f] : RelativelyAmpleLineBundle f L := by
  refine ⟨inferInstance, hL.2.1, fun U hU ↦ ?_⟩
  let : IsAffine U.toScheme := hU
  have : IsAffineHom (f ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U) inferInstance
  exact hL.restrict_affine _

/-- The relative and absolute section definitions agree over an affine base. -/
theorem relativelyAmpleLineBundle_iff_of_affine (f : X ⟶ S)
    [IsAffine S] [QuasiCompact f] : RelativelyAmpleLineBundle f L ↔ AmpleLineBundle L :=
  ⟨RelativelyAmpleLineBundle.ample_of_affine, fun h ↦ h.relative_of_affine f⟩

end FLT.Mazur.FCurve
