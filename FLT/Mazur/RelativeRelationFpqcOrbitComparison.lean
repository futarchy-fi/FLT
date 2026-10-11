/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationInvariantLocallyRinged
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The actual orbit space of a faithfully flat kernel pair

A quasi-compact faithfully flat scheme map identifies its target topology with
the original full relation orbit topology. This retains the original source
projection and does not use preservation of pullbacks by underlying points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U T : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (g : U ⟶ T)
  (H : IsPullback p q g g)

/-- The original invariant locally ringed quotient maps to the specified scheme target. -/
def kernelQuotientComparison : invariantLocallyRingedSpace e ⟶ T.left.toLocallyRingedSpace :=
  (invariantLocallyRingedIso e).inv ≫
    coequalizer.desc g.left.toLRSHom (congrArg (fun k ↦ k.left.toLRSHom) H.w)

/-- The comparison preserves the original source map, including its regular functions. -/
@[reassoc]
theorem kernelQuotientComparison_projection :
    invariantLocallyRingedProjection e ≫ kernelQuotientComparison e g H =
      g.left.toLRSHom := by
  dsimp only [kernelQuotientComparison, invariantLocallyRingedProjection]
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact coequalizer.π_desc _ _

/-- The continuous comparison preserves every original source point. -/
theorem kernelQuotientComparison_apply (x : U.left) :
    (kernelQuotientComparison e g H).base (projection e x) = g.left x := by
  have h := congrArg (fun k ↦ k.base)
    (kernelQuotientComparison_projection e g H)
  rw [LocallyRingedSpace.comp_base, invariantLocallyRingedProjection_base] at h
  exact congrArg (fun k ↦ k x) h

/-- Full kernel pairs identify exactly the original point fibers. -/
theorem kernelQuotientComparison_injective :
    Function.Injective (kernelQuotientComparison e g H).base := by
  intro x y h
  obtain ⟨a, rfl⟩ := projection_surjective e x
  obtain ⟨b, rfl⟩ := projection_surjective e y
  rw [kernelQuotientComparison_apply, kernelQuotientComparison_apply] at h
  obtain ⟨r, hr, hs⟩ := Scheme.exists_preimage_of_isPullback (H.map (Over.forget S)) a b h
  exact (projection_eq_iff e a b).mpr ⟨r, hr, hs⟩

variable [Flat g.left] [QuasiCompact g.left] [Surjective g.left]

/-- The comparison is a quotient map, using faithful flatness of the original scheme map. -/
theorem kernelQuotientComparison_isQuotientMap :
    IsQuotientMap (kernelQuotientComparison e g H).base := by
  apply (projection_isQuotientMap e).of_comp_isQuotientMap
  have he : (kernelQuotientComparison e g H).base ∘ projection e = g.left :=
    funext (kernelQuotientComparison_apply e g H)
  rw [he]
  exact Flat.isQuotientMap_of_surjective g.left

/-- The comparison is an isomorphism of topological spaces, not merely a point bijection. -/
instance kernelQuotientComparison_base_isIso : IsIso (kernelQuotientComparison e g H).base :=
  TopCat.isIso_of_bijective_of_isOpenMap _
    ⟨kernelQuotientComparison_injective e g H,
      (kernelQuotientComparison_isQuotientMap e g H).surjective⟩
    ((kernelQuotientComparison_isQuotientMap e g H).isCoinducing.isOpenMap_of_injective
      (kernelQuotientComparison_injective e g H))

end FLT.Mazur.RelativeRelationOrbit
