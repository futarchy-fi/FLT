/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationPrincipalFullInvariants
public import FLT.Mazur.SchemeRelationInvariantSpectrum

/-!
# The actual principal localization of the invariant affine candidate

The invariant spectrum of the full principal restriction maps by an open
immersion to the original invariant spectrum. The square with both original
source projections commutes as scheme maps, retaining the entire sheaf map.
This is compatibility of candidates, not effectiveness of either candidate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationPrincipalLocalization
open SchemeEffectiveEpiSections SchemeRelationRestriction SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
variable {D A : Scheme.{u}} (p q : D ⟶ A) (s : compatibleFunctions p q)
  [CompactSpace A] [QuasiSeparatedSpace A] [CompactSpace D] [QuasiSeparatedSpace D]
local notation "W" => A.basicOpen s.val
local notation "p'" => fst p q (Scheme.Opens.ι (A.basicOpen s.val))
local notation "q'" => snd p q (Scheme.Opens.ι (A.basicOpen s.val))

/-- The original invariant restriction homomorphism in full-relation coordinates. -/
def candidateRestriction : CommRingCat.of (compatibleFunctions p q) ⟶
    CommRingCat.of (compatibleFunctions p' q') :=
  CommRingCat.ofHom ((fullEquiv p q s).toRingHom.comp
    (algebraMap (compatibleFunctions p q) (Localization.Away s)))

/-- The invariant affine candidate of the full restriction maps to the original candidate. -/
def candidateOpenMap : target p' q' ⟶ target p q := Spec.map (candidateRestriction p q s)

/-- The full restricted candidate is an actual open subscheme of the original candidate. -/
instance candidateOpenMap_isOpenImmersion : IsOpenImmersion (candidateOpenMap p q s) := by
  change IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (algebraMap (compatibleFunctions p q) (Localization.Away s)) ≫
      (fullEquiv p q s).toCommRingCatIso.hom))
  rw [Spec.map_comp]
  let _ := IsOpenImmersion.of_isLocalization (S := Localization.Away s) s
  infer_instance

/-- The new invariant inclusion is the actual original coefficient restriction. -/
theorem candidateRestriction_inclusion :
    candidateRestriction p q s ≫ inclusion p' q' = inclusion p q ≫ (W).ι.appTop := by
  ext a
  exact fullEquiv_algebraMap p q s a

/-- Localized candidate projections commute with the original source-open inclusion. -/
@[reassoc]
theorem candidateOpenMap_projection :
    projection p' q' ≫ candidateOpenMap p q s = (W).ι ≫ projection p q := by
  simp only [projection, candidateOpenMap, Category.assoc, ← Spec.map_comp]
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rw [candidateRestriction_inclusion]

end FLT.Mazur.SchemeRelationPrincipalLocalization
