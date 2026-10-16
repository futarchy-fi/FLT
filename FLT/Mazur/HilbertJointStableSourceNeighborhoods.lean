/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertNormalizedLabelCharts
public import FLT.Mazur.EquivalenceRelationJointFrameCover

/-!
# Exhaustive stable common-source neighborhoods for the original Hilbert relation

Every original mixed-frame arrow over an invariant domain has an affine etale
common-frame neighborhood stable under its full finite label action. Its charts
transport coherently to all distinguished labels. Neither endpoint frame needs
to be complete. The lifting-multiplier coefficient identity remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k

/-- Stable affine common sources exhaust every mixed Hilbert arrow in the original domain. -/
theorem exists_joint_stable_source_neighborhood
    {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
    (W : A.left.Opens) (hW : (p) ⁻¹ᵁ W = (q) ⁻¹ᵁ W)
    (x : MixedFrames.relation p q I J o o')
    (hx : first p q I o (MixedFrames.fst p q I J o o' x) ∈ W) :
    ∃ (a : MixedFrames.JointIndex I J)
      (U : (j : Fin a.1.val) → (source p q (Fin a.1.val) j).Opens),
      (∀ j, IsAffineOpen (U j)) ∧
      (∀ j σ, (action e (Fin a.1.val) j σ).hom ⁻¹ᵁ U j = U j) ∧
      (∀ j, U j ≤ first p q (Fin a.1.val) j ⁻¹ᵁ W) ∧
      (∀ j j', labelChange e (Fin a.1.val) j j' ⁻¹ᵁ U j' = U j) ∧
      Etale ((U (a.2.val.1 o)).ι ≫ MixedFrames.jointMap e o o' a) ∧
      ∃ y : (U (a.2.val.1 o)).toScheme,
        ((U (a.2.val.1 o)).ι ≫ MixedFrames.jointMap e o o' a) y = x := by
  obtain ⟨a, y, hy⟩ := MixedFrames.jointMap_covers e o o' x
  have hyW : normalizedFullRelationFirst f hL d V c k a.1.val (a.2.val.1 o) y ∈ W := by
    have hbase := congrArg (fun g ↦ g y)
      (MixedFrames.jointGraph_first e o o' a.2.val.1 a.2.val.2)
    change first p q I o (MixedFrames.fst p q I J o o'
      (MixedFrames.jointMap e o o' a y)) = first p q (Fin a.1.val) (a.2.val.1 o) y at hbase
    change first p q (Fin a.1.val) (a.2.val.1 o) y ∈ W
    rw [← hbase, hy]
    exact hx
  obtain ⟨U, hyU, hU, hstable, hdomain, _, hlabel⟩ :=
    exists_normalized_label_chart_family f hL d V c k a.1.val (a.2.val.1 o) W hW y hyW
  refine ⟨a, U, hU, hstable, hdomain, hlabel, ?_, ⟨y, hyU⟩, ?_⟩
  · infer_instance
  · exact hy

end FLT.Mazur.HilbertChart.AffineRestriction
