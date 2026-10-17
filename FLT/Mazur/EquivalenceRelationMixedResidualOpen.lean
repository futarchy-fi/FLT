/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationSubframeComparison
public import FLT.Mazur.DisjointClosedCoproduct
public import FLT.Mazur.EquivalenceRelationCompleteThickenings
public import FLT.Mazur.PolygonDivisorPowerPullback

/-!
# Residual branches for independent frame labels and sizes

If the second normalized source is separated, the full mixed first projection
is separated. The finite subframe comparison is therefore both open and closed.
Its actual residual complement retains all other original arrows. Complete
first fibers miss the residual complement, with no condition on the size or
completeness of the independent second frame.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
local notation "r" => fst p q I J o o'
local notation "s" => snd p q I J o o'

include e in
/-- The two independent mixed endpoints embed the entire relation into their product. -/
theorem mixedEndpointPair_mono : Mono (pullback.lift (r) (s)
    (show (r) ≫ terminal.from _ = (s) ≫ terminal.from _ from terminal.hom_ext _ _)) := by
  constructor
  intro T u v h
  apply hom_ext p q I J o o' e
  · simpa only [Category.assoc, pullback.lift_fst] using
      congrArg (fun a ↦ a ≫ pullback.fst _ _) h
  · simpa only [Category.assoc, pullback.lift_snd] using
      congrArg (fun a ↦ a ≫ pullback.snd _ _) h

variable [(source p q J o').IsSeparated]

include e in
/-- Only separatedness of the independent second source is needed for the full projection. -/
theorem mixedFirst_separated : IsSeparated r := by
  let _ := mixedEndpointPair_mono e o o'
  have : IsSeparated (pullback.lift (r) (s)
      (show (r) ≫ terminal.from _ = (s) ≫ terminal.from _ from terminal.hom_ext _ _) ≫
      pullback.fst _ _) := inferInstance
  rwa [pullback.lift_fst] at this

/-- Every actual subframe section is closed, even for unequal frame sizes. -/
theorem subframeGraph_closed (ι : J ↪ I) : IsClosedImmersion (subframeGraph e o o' ι) := by
  let _ := mixedFirst_separated e o o'
  exact UnramifiedSectionImmersion.isClosedImmersion (r) _ (subframeGraph_fst e o o' ι)

variable [Etale p]

/-- The finite comparison is a closed immersion into the unchanged whole mixed relation. -/
theorem embeddingComparison_closed : IsClosedImmersion (embeddingComparison e o o') := by
  let _ := fun ι ↦ subframeGraph_closed e o o' ι
  exact DisjointClosedCoproduct.closed (subframeGraph e o o')
    (fun _ _ h ↦ subframeGraph_disjoint e o o' _ _ h)

/-- All original mixed arrows outside the finite subframe comparison form an actual open. -/
def mixedResidualOpen : (relation p q I J o o').Opens := by
  let _ := embeddingComparison_closed e o o'
  exact ⟨(Set.range (embeddingComparison e o o'))ᶜ,
    (embeddingComparison e o o').isClosedEmbedding.isClosed_range.isOpen_compl⟩

/-- The residual complement keeps exactly the arrows outside the whole finite comparison. -/
theorem mem_mixedResidualOpen (x : relation p q I J o o') :
    x ∈ mixedResidualOpen e o o' ↔ x ∉ Set.range (embeddingComparison e o o') := Iff.rfl

/-- No residual mixed arrow has complete first frame, regardless of the second frame size. -/
theorem mixedResidualOpen_first_incomplete (x : (mixedResidualOpen e o o').toScheme) :
    ((mixedResidualOpen e o o').ι ≫ (r)) x ∉
      completePointLocus (p := p) (q := q) I o := by
  intro hx
  let v := (relation p q I J o o').fromSpecResidueField x.val
  have hv : Complete I o (v ≫ (r)) := by
    rw [complete_iff_mem_completePointLocus]
    change (r) ((relation p q I J o o').fromSpecResidueField x.val default) ∈ _
    rw [Scheme.fromSpecResidueField_apply]
    exact hx
  obtain ⟨w, hw⟩ := complete_factors_embeddingComparison e o o' v hv
  apply (mem_mixedResidualOpen e o o' x.val).mp x.property
  refine ⟨w default, ?_⟩
  exact (congrArg (fun f ↦ f default) hw).trans (Scheme.fromSpecResidueField_apply _ _)

/-- Arbitrary independent source restrictions retain this same residual open by base change. -/
def mixedResidualTestOpen {T : Scheme.{0}} (z : T ⟶ relation p q I J o o') : T.Opens :=
  z ⁻¹ᵁ mixedResidualOpen e o o'

/-- The pulled-back residual part still has no complete first-endpoint fibers. -/
theorem mixedResidualTestOpen_first_incomplete {T : Scheme.{0}}
    (z : T ⟶ relation p q I J o o') (x : (mixedResidualTestOpen e o o' z).toScheme) :
    ((mixedResidualTestOpen e o o' z).ι ≫ z ≫ (r)) x ∉
      completePointLocus (p := p) (q := q) I o :=
  mixedResidualOpen_first_incomplete e o o' ⟨z x.val, x.property⟩

/-- The complete first ideal is the unit ideal on all independent mixed residual branches. -/
theorem mixedResidual_completeIdeal_eq_top :
    (completeSupportIdeal (p := p) (q := q) I o).comap
      ((mixedResidualOpen e o o').ι ≫ (r)) = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  apply TopologicalSpace.Closeds.ext
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact mixedResidualOpen_first_incomplete e o o' x hx

/-- No complete ideal power constrains the residual mixed equations, even for unequal sizes. -/
theorem mixedResidual_completeIdeal_pow_eq_top (n : ℕ) :
    (completeSupportIdeal (p := p) (q := q) I o ^ n).comap
      ((mixedResidualOpen e o o').ι ≫ (r)) = ⊤ := by
  rw [FCurve.idealSheaf_comap_pow, mixedResidual_completeIdeal_eq_top]
  exact one_pow n

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
