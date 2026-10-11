/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationFpqcSectionComparison

/-!
# Faithfully flat kernel pairs have the original invariant locally ringed quotient

The topology comparison and the actual regular-function comparison are both
isomorphisms. Thus the explicitly constructed invariant quotient is the target
scheme as a locally ringed space, not merely as a scheme coequalizer.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U T : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (g : U ⟶ T)
  (H : IsPullback p q g g)
  [Flat g.left] [QuasiCompact g.left] [Surjective g.left]

/-- Every section map of the original quotient comparison is an isomorphism. -/
instance kernelQuotientComparison_app_isIso (W : T.left.Opens) :
    IsIso ((kernelQuotientComparison e g H).c.app (op W)) := by
  have he : (kernelQuotientComparison e g H).c.app (op W) =
      (fpqcInvariantSectionsEquiv e g H W).symm.toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    apply (fpqcInvariantSectionsEquiv e g H W).injective
    exact (fpqcInvariantSectionsEquiv_comparison e g H W s).trans
      ((fpqcInvariantSectionsEquiv e g H W).apply_symm_apply s).symm
  rw [he]
  infer_instance

/-- The invariant quotient comparison is an actual locally ringed-space isomorphism. -/
instance kernelQuotientComparison_isIso : IsIso (kernelQuotientComparison e g H) := by
  let _ (W : (TopologicalSpace.Opens T.left)ᵒᵖ) :
      IsIso ((kernelQuotientComparison e g H).c.app W) :=
    kernelQuotientComparison_app_isIso e g H W.unop
  let _ : IsIso (kernelQuotientComparison e g H).c :=
    NatIso.isIso_of_isIso_app _
  let hc : IsIso (kernelQuotientComparison e g H).toHom :=
    PresheafedSpace.isIso_of_components _
  let _ : IsIso (SheafedSpace.forgetToPresheafedSpace.map
      (kernelQuotientComparison e g H).toShHom) :=
    hc
  let hs : IsIso (kernelQuotientComparison e g H).toShHom :=
    isIso_of_reflects_iso _ SheafedSpace.forgetToPresheafedSpace
  let _ : IsIso (LocallyRingedSpace.forgetToSheafedSpace.map
      (kernelQuotientComparison e g H)) :=
    hs
  exact isIso_of_reflects_iso _ LocallyRingedSpace.forgetToSheafedSpace

/-- The original invariant quotient, including its structure sheaf, is the target scheme. -/
def fpqcInvariantQuotientIso : invariantLocallyRingedSpace e ≅ T.left.toLocallyRingedSpace :=
  asIso (kernelQuotientComparison e g H)

/-- The effective quotient retains the original source projection. -/
@[reassoc]
theorem fpqcInvariantQuotientIso_projection :
    invariantLocallyRingedProjection e ≫ (fpqcInvariantQuotientIso e g H).hom =
      g.left.toLRSHom := kernelQuotientComparison_projection e g H

/-- The represented invariant quotient retains the original relative structural map. -/
theorem fpqcInvariantQuotientIso_baseMap :
    (fpqcInvariantQuotientIso e g H).hom ≫ T.hom.toLRSHom =
      invariantLocallyRingedBaseMap e := by
  let _ : Epi (invariantLocallyRingedProjection e) := by
    unfold invariantLocallyRingedProjection locallyRingedProjection
    infer_instance
  apply (cancel_epi (invariantLocallyRingedProjection e)).mp
  rw [← Category.assoc, fpqcInvariantQuotientIso_projection,
    invariantLocallyRingedProjection_baseMap]
  exact congrArg Scheme.Hom.toLRSHom (Over.w g)

end FLT.Mazur.RelativeRelationOrbit
