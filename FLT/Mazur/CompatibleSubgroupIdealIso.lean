/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIso

/-!
# Compatible subgroup isomorphisms from equal actual ideals

Two closed subgroup schemes on the same curve with identical kernel ideals
are compatibly isomorphic. The subgroup group law is recovered by cancelling
its monomorphic inclusion into the smooth group.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

variable {S : Scheme} {n : ℕ} {E : GeneralizedEllipticCurve S}
  (H J : E.FiniteSubgroup n)

/-- Equal closed subgroup ideals give an isomorphism preserving both inclusions and group laws. -/
def compatibleIsoOfIdealEq (h : H.ideal = J.ideal) : CompatibleIso H J := by
  have he : J.curveMap.left.ker = H.curveMap.left.ker := h.symm
  let f := IsClosedImmersion.lift J.curveMap.left H.curveMap.left he.le
  have hf : f ≫ J.curveMap.left = H.curveMap.left := IsClosedImmersion.lift_fac _ _ _
  have : IsIso f := IsClosedImmersion.isIso_lift _ _ he
  let d : H.carrier ≅ J.carrier := Over.isoMk (asIso f) (by
    change f ≫ J.carrier.hom = H.carrier.hom
    rw [← J.curveMap.w, ← Category.assoc, hf, H.curveMap.w])
  have hd : d.hom ≫ J.curveMap = H.curveMap := by
    apply Over.OverMorphism.ext
    exact hf
  have : Mono E.inclusion := Over.mono_of_mono_left E.inclusion
  have : Mono J.inclusion := Over.mono_of_mono_left J.inclusion
  have hi : d.hom ≫ J.inclusion = H.inclusion := by
    apply (cancel_mono E.inclusion).mp
    simpa only [Category.assoc, curveMap] using hd
  let _ : IsMonHom d.hom :=
    { one_hom := by
        apply (cancel_mono J.inclusion).mp
        rw [Category.assoc, hi, IsMonHom.one_hom, IsMonHom.one_hom]
      mul_hom := by
        apply (cancel_mono J.inclusion).mp
        rw [Category.assoc, hi, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom,
          tensorHom_comp_tensorHom_assoc, hi] }
  refine ⟨Iso.refl E, d, ?_⟩
  change H.curveMap ≫ 𝟙 E.curve = d.hom ≫ J.curveMap
  simpa only [Category.comp_id] using hd.symm

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
