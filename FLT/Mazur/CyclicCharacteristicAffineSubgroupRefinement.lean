/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSubgroup
public import FLT.Mazur.CyclicCharacteristicAffineEquationCoherence
public import FLT.Mazur.CompatibleSubgroupBaseChangeCompEq

/-!
# Compatible affine subgroup refinement

Refining a normalized affine chart preserves the original full subgroup,
and its full curve map is the actual coefficient-model comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool) {A B : Type} [CommRing A] [CommRing B]
  (q : Spec (.of A) ⟶ normalizedLocus n b) (f : A →+* B)
local notation "k" => Spec.map (CommRingCat.ofHom f)

/-- The actual finite subgroups on refined affine equations compare compatibly. -/
def affineSubgroupRefinement : CompatibleIso (affineSubgroup n b (k ≫ q))
    ((affineSubgroup n b q).baseChange k) :=
  (affineSubgroupComparison n b (k ≫ q)).trans
    ((compatibleBaseChangeComp (normalizedSubgroup n b) q k).trans
      ((affineSubgroupComparison n b q).baseChange k).symm)

/-- The compatible refinement retains exactly the full affine coefficient-model map. -/
theorem affineSubgroupRefinement_curve :
    (affineSubgroupRefinement n b q f).curve = affineModelPullbackIso n b q f := by
  apply Iso.ext
  change ((affineEquationIso n b (k ≫ q)).hom ≫
    ((normalizedCurve n b).baseChangeCompIso q k).hom) ≫
      baseChangeMap k (affineEquationIso n b q).inv = _
  rw [affineEquationIso_refine]
  change (_ ≫ ((baseChangeFunctor k).mapIso (affineEquationIso n b q)).hom) ≫
    ((baseChangeFunctor k).mapIso (affineEquationIso n b q)).inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.CyclicCharacteristicAtlas
