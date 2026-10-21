/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupPullbackCast

/-!
# Full subgroup comparisons determined by a cartesian curve projection

A cartesian presentation of the target whole curve detects equality of
compatible subgroup comparisons from their original-curve projection.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S X Y : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}

/-- A cartesian original-curve projection detects the entire compatible subgroup comparison. -/
theorem CompatibleIso.ext_curve_projection (a b : CompatibleIso H J)
    (i : F.curve.left ⟶ X) (f : X ⟶ Y) (g : S ⟶ Y)
    (hp : IsPullback i F.curve.hom f g)
    (h : a.curve.hom.curve.left ≫ i = b.curve.hom.curve.left ≫ i) : a = b := by
  apply CompatibleIso.ext_curve_hom
  apply GeneralizedEllipticCurve.forgetCurve.map_injective
  apply Over.OverMorphism.ext
  apply hp.hom_ext
  · exact h
  · exact (Over.w _).trans (Over.w _).symm

/-- A comparison followed by a pulled-back comparison retains its original curve projection. -/
@[reassoc] theorem CompatibleIso.trans_baseChange_curve_fst {T : Scheme} (g : T ⟶ S)
    {D : GeneralizedEllipticCurve T} {K : D.FiniteSubgroup n}
    (a : CompatibleIso K (H.baseChange g)) (b : CompatibleIso H J) :
    (a.trans (b.baseChange g)).curve.hom.curve.left ≫ pullback.fst F.curve.hom g =
      a.curve.hom.curve.left ≫ pullback.fst E.curve.hom g ≫ b.curve.hom.curve.left := by
  change (a.curve.hom.curve.left ≫
    (GeneralizedEllipticCurve.baseChangeMap g b.curve.hom).curve.left) ≫ _ = _
  rw [Category.assoc, GeneralizedEllipticCurve.baseChangeMap_fst]

/-- A compatible equal-composite comparison preserves the original full curve projection. -/
@[reassoc] theorem CompatibleIso.trans_compEq_curve_fst {T U : Scheme}
    (p : T ⟶ S) (q : U ⟶ T) (f : U ⟶ S) (w : f = q ≫ p)
    {D : GeneralizedEllipticCurve U} {K : D.FiniteSubgroup n}
    (a : CompatibleIso K (H.baseChange f)) :
    (a.trans (compatibleBaseChangeCompEq H p q f w)).curve.hom.curve.left ≫
        pullback.fst (E.baseChange p).curve.hom q ≫ pullback.fst E.curve.hom p =
      a.curve.hom.curve.left ≫ pullback.fst E.curve.hom f := by
  change (a.curve.hom.curve.left ≫ (compatibleBaseChangeCompEq H p q f w).curve.hom.curve.left)
    ≫ _ ≫ _ = _
  rw [Category.assoc, compatibleBaseChangeCompEq_curve_fst]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
