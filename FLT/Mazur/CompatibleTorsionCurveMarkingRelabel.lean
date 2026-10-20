/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorTorsionLocalRelabel

/-!
# Local cyclic marking matches retain the original curve comparison

The actual subgroup generator equality is transported through its original
inclusion into the smooth curve group. Every label and the given full family
isomorphism are retained; no subgroup etaleness assumption is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n]
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}
  [IsSeparated F.group.hom] [LocallyOfFiniteType F.group.hom]
  [FormallyUnramified (GroupTorsionScheme.scheme F.group n).hom]
  (a : CompatibleIso H J)
  {P : 𝟙_ (Over S) ⟶ H.carrier} {Q : 𝟙_ (Over S) ⟶ J.carrier}

/-- The local cyclic relabeling preserves every original curve-group section. -/
theorem CompatibleIso.exists_local_curveMarking_relabel_of_torsion
    (hP : H.IsCartierGenerator P) (hQ : J.IsCartierGenerator Q) (x : S) :
    ∃ (r : MulAut (Multiplicative (ZMod n))) (U : S.Opens),
      IsAffineOpen U ∧ x ∈ U ∧ ∀ i,
        U.ι ≫ (H.generatorCurveMarking hP (r i)).left ≫ a.curve.hom.group.left =
          U.ι ≫ (J.generatorCurveMarking hQ i).left := by
  obtain ⟨r, U, hU, hx, he⟩ := a.exists_local_generator_relabel_of_torsion hP hQ x
  refine ⟨r, U, hU, hx, fun i => ?_⟩
  have hinc : H.inclusion.left ≫ a.curve.hom.group.left =
      a.subgroup.hom.left ≫ J.inclusion.left := congrArg Over.Hom.left a.group_inclusion
  change U.ι ≫ ((P ^ (r i).toAdd.val).left ≫ H.inclusion.left) ≫
      a.curve.hom.group.left = U.ι ≫ (Q ^ i.toAdd.val).left ≫ J.inclusion.left
  have h := congrArg (· ≫ J.inclusion.left) (he i)
  simpa only [Category.assoc, hinc] using h

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
