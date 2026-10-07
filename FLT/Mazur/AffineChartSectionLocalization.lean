/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePieceSectionLocalization

/-!
# Localization over the coordinate ring of an affine chart

The original section restriction on a principal subopen localizes over the
chart's own coordinate ring, without requiring that ring to act globally.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.AffineChartSectionLocalization

variable {X : Scheme.{u}} (M : X.Modules) (V : X.affineOpens)

/-- Original sections, with scalars restricted from one fixed affine chart. -/
abbrev sections (W : X.Opens) (h : W ≤ V.1) : ModuleCat Γ(X, V.1) :=
  (ModuleCat.restrictScalars (X.presheaf.map (homOfLE h).op).hom).obj (M.val.obj (op W))

/-- The original restriction as a linear map over the fixed chart coordinate ring. -/
def restriction {W T : X.Opens} (hW : W ≤ V.1) (hT : T ≤ V.1) (i : W ⟶ T) :
    sections M V T hT →ₗ[Γ(X, V.1)] sections M V W hW where
  toFun := M.presheaf.map i.op
  map_add' := map_add _
  map_smul' r s := by
    change M.presheaf.map i.op (X.presheaf.map (homOfLE hT).op r • s) = _
    rw [M.map_smul]
    rw [← Functor.map_comp_apply]
    rfl

/-- Spectrum coordinates of any chart subopen keep its original scalar action. -/
def imageSectionsEquiv (W : (Spec Γ(X, V.1)).Opens) :
    Γ(M.restrict V.2.fromSpec, W) ≃ₗ[Γ(X, V.1)]
      sections M V (V.2.fromSpec ''ᵁ W)
        (by simpa only [V.2.opensRange_fromSpec] using
          (show V.2.fromSpec ''ᵁ W ≤ V.2.fromSpec.opensRange from
            Set.image_subset_range _ _)) := by
  refine { (M.restrictAppIso V.2.fromSpec W).addCommGroupIsoToAddEquiv with
    map_smul' := ?_ }
  intro r s
  change Γ(M, V.2.fromSpec ''ᵁ W) at s
  change (V.2.fromSpec.appIso W).inv
    ((Spec Γ(X, V.1)).presheaf.map W.leTop.op ((Scheme.ΓSpecIso Γ(X, V.1)).inv r)) • s =
      (X.presheaf.map (homOfLE _).op r : Γ(X, V.2.fromSpec ''ᵁ W)) • s
  congr 1
  have h := V.2.fromSpec.appLE_appIso_inv
    (show W ≤ V.2.fromSpec ⁻¹ᵁ V.1 by rw [V.2.fromSpec_preimage_self]; exact le_top)
  have hr := ConcreteCategory.congr_hom h r
  simpa only [Scheme.Hom.appLE, V.2.fromSpec_app_self, CommRingCat.comp_apply,
    ← Functor.map_comp_apply, ← op_comp, homOfLE_comp_eqToHom,
    TopologicalSpace.Opens.leTop] using hr

/-- The spectrum coordinates intertwine the actual restriction maps. -/
lemma imageSectionsEquiv_restrict {W T : (Spec Γ(X, V.1)).Opens} (i : W ⟶ T)
    (s : Γ(M.restrict V.2.fromSpec, T)) :
    imageSectionsEquiv M V W ((M.restrict V.2.fromSpec).presheaf.map i.op s) =
      restriction M V _ _ (V.2.fromSpec.opensFunctor.map i)
        (imageSectionsEquiv M V T s) := rfl

/-- Equality of subopens transports the original chart-linear localization statement. -/
lemma restriction_isLocalized_congr (r : Γ(X, V.1))
    {W T W' T' : X.Opens} (hW : W ≤ V.1) (hT : T ≤ V.1)
    (hW' : W' ≤ V.1) (hT' : T' ≤ V.1) (i : W ⟶ T) (i' : W' ⟶ T')
    (eW : W = W') (eT : T = T') :
    IsLocalizedModule.Away r (restriction M V hW hT i) ↔
      IsLocalizedModule.Away r (restriction M V hW' hT' i') := by
  subst W'; subst T'
  cases Subsingleton.elim i i'
  rfl

/-- All quasi-coherent sections localize over the actual affine chart coordinates. -/
lemma restriction_isLocalized [M.IsQuasicoherent] (r : Γ(X, V.1)) :
    IsLocalizedModule.Away r
      (restriction M V (X.basicOpen_le r) le_rfl (homOfLE (X.basicOpen_le r))) := by
  let e := imageSectionsEquiv M V ⊤
  let e' := imageSectionsEquiv M V (PrimeSpectrum.basicOpen r)
  have h := IsLocalizedModule.of_linearEquiv (.powers r)
    (ModuleSheafTensor.affineRestriction (M.restrict V.2.fromSpec) r) e'
  let i := V.2.fromSpec.opensFunctor.map
    (homOfLE (show PrimeSpectrum.basicOpen r ≤ ⊤ from le_top))
  have h' : IsLocalizedModule.Away r ((restriction M V _ _ i).comp e.toLinearMap) := h
  have h'' := (IsLocalizedModule.comp_iff_of_bijective_right (.powers r)
    e.toLinearMap e.bijective).mp h'
  exact (restriction_isLocalized_congr M V r _ _ _ _ i _
    (V.2.fromSpec_image_basicOpen r)
    (V.2.fromSpec.image_top_eq_opensRange.trans V.2.opensRange_fromSpec)).mp h''

end FLT.Mazur.AffineChartSectionLocalization
