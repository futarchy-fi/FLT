/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicGeometricOrbit
public import FLT.Mazur.CyclicCharacteristicProductOperationSchemes
public import FLT.Mazur.GeometricPointCoverCriterion

/-!
# Topological endpoints of the full same-chart comparison scheme

Use algebraic closures of actual arrow residue fields. Every underlying arrow
point has endpoints in one finite relabeling orbit, without a reducedness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b : Bool)

/-- Every geometric map to the full comparison scheme has relabeled endpoints. -/
theorem productScheme_geometric_sameChart_orbit {K : Type} [Field K] [IsAlgClosed K]
    (p : Spec (.of K) ⟶ productSubgroupScheme n b b) :
    ∃ e : RelabelGroup n,
      (p ≫ productArrowSource n b b) ≫ (normalizedRelabelAction n b e).hom =
        p ≫ productArrowTarget n b b := by
  apply productArrow_geometric_sameChart_orbit
  refine ⟨p, ?_⟩
  apply prod.hom_ext <;>
    simp only [Category.assoc, prod.lift_fst, prod.lift_snd,
      productArrowSource, productArrowTarget]

/-- Every actual arrow point has endpoints in the same finite relabeling orbit. -/
theorem productScheme_point_sameChart_orbit (x : productSubgroupScheme n b b) :
    ∃ e : RelabelGroup n,
      (normalizedRelabelAction n b e).hom (productArrowSource n b b x) =
        productArrowTarget n b b x := by
  let X := productSubgroupScheme n b b
  let K := AlgebraicClosure (X.residueField x)
  let p : Spec (.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
      X.fromSpecResidueField x
  obtain ⟨e, he⟩ := productScheme_geometric_sameChart_orbit n b p
  refine ⟨e, ?_⟩
  have hp : p (IsLocalRing.closedPoint K) = x := X.fromSpecResidueField_apply x _
  have h := congrArg (fun k ↦ k (IsLocalRing.closedPoint K)) he
  change (normalizedRelabelAction n b e).hom
    (productArrowSource n b b (p (IsLocalRing.closedPoint K))) =
      productArrowTarget n b b (p (IsLocalRing.closedPoint K)) at h
  rwa [hp] at h

end FLT.Mazur.CyclicCharacteristicAtlas
