/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleAffinePullback

/-!
# Transport of ampleness from an open subscheme to its image

The pullback composition isomorphisms identify a twice-restricted line
with the line on its image open. These lemmas keep that identification
explicit when shrinking affine base neighborhoods.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

/-- Pullback along a scheme isomorphism reflects and preserves ampleness. -/
theorem ampleLineBundle_pullback_iso_iff {X Y : Scheme.{u}} (e : Y ≅ X)
    (L : X.Modules) : AmpleLineBundle ((pullback e.hom).obj L) ↔ AmpleLineBundle L := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.pullback_affine e.hom⟩
  exact (h.pullback_affine e.inv).of_iso
    (((pullbackComp e.inv e.hom).app L ≪≫
      (pullbackCongr e.inv_hom_id).app L ≪≫ (pullbackId X).app L).symm)

/-- Ampleness on a restricted open immersion is ampleness on its image open. -/
theorem ampleLineBundle_openImage {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : Y.Opens) (L : X.Modules)
    (h : AmpleLineBundle ((pullback U.ι).obj ((pullback j).obj L))) :
    AmpleLineBundle ((pullback (j ''ᵁ U).ι).obj L) := by
  apply (ampleLineBundle_pullback_iso_iff (j.isoImage U) _).mp
  exact h.of_iso ((pullbackComp (j.isoImage U).hom (j ''ᵁ U).ι).app L ≪≫
    (pullbackCongr (Scheme.Hom.isoImage_hom_ι j U)).app L ≪≫
    ((pullbackComp U.ι j).app L).symm)

/-- Twice restricting the base proves ampleness on the corresponding original base open. -/
theorem ampleLineBundle_baseOpenImage {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) (U : V.toScheme.Opens) (L : X.Modules)
    (h : AmpleLineBundle ((pullback ((f ∣_ V) ⁻¹ᵁ U).ι).obj
      ((pullback (f ⁻¹ᵁ V).ι).obj L))) :
    AmpleLineBundle ((pullback (f ⁻¹ᵁ (V.ι ''ᵁ U)).ι).obj L) := by
  have ha := ampleLineBundle_openImage (f ⁻¹ᵁ V).ι ((f ∣_ V) ⁻¹ᵁ U) L h
  rwa [image_morphismRestrict_preimage] at ha

end FLT.Mazur.FCurve
