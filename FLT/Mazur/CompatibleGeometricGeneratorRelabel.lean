/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorGeometricPowers
public import FLT.Mazur.CompatibleSubgroupGeneratorMarking
public import FLT.Mazur.CyclicUnitRelabeling

/-!
# Full compatible comparisons determine geometric cyclic relabelings

Transport through an actual compatible curve and subgroup isomorphism, then
compare the original Cartier generators. One full-level automorphism matches
every cyclic label in the subgroup and in the smooth group of the curve.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
variable {K : Type} [Field K] [IsAlgClosed K]
  {E F : GeneralizedEllipticCurve (Spec (.of K))} {n : ℕ} [NeZero n]
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n} (a : CompatibleIso H J)
  {P : 𝟙_ (Over (Spec (.of K))) ⟶ H.carrier}
  {Q : 𝟙_ (Over (Spec (.of K))) ⟶ J.carrier}

/-- One cyclic automorphism matches all original powers under the full subgroup comparison. -/
theorem CompatibleIso.exists_geometric_generator_relabel
    (hP : H.IsCartierGenerator P) (hQ : J.IsCartierGenerator Q) :
    ∃ e : MulAut (Multiplicative (ZMod n)), ∀ i,
      (P ^ (e i).toAdd.val) ≫ a.subgroup.hom = Q ^ i.toAdd.val := by
  obtain ⟨u, hu⟩ := (a.cartierGenerator hP).exists_unit_power J hQ
  refine ⟨CyclicUnitRelabeling.labelAut u, fun i ↦ ?_⟩
  rw [pow_comp, CyclicUnitRelabeling.relabeled_power _ (a.cartierGenerator hP).1, hu]

/-- The same relabeling retains every original curve-group marking. -/
theorem CompatibleIso.exists_geometric_curveMarking_relabel
    (hP : H.IsCartierGenerator P) (hQ : J.IsCartierGenerator Q) :
    ∃ e : MulAut (Multiplicative (ZMod n)), ∀ i,
      H.generatorCurveMarking hP (e i) ≫ a.curve.hom.group =
        J.generatorCurveMarking hQ i := by
  obtain ⟨e, he⟩ := a.exists_geometric_generator_relabel hP hQ
  refine ⟨e, fun i ↦ ?_⟩
  change ((P ^ (e i).toAdd.val) ≫ H.inclusion) ≫ a.curve.hom.group =
    (Q ^ i.toAdd.val) ≫ J.inclusion
  rw [Category.assoc, a.group_inclusion, ← Category.assoc, he]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
