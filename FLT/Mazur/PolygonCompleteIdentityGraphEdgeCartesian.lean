/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionGraphSmooth
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicEdge

/-!
# The original outgoing edge is the full graph preimage

The complete graph is already unchanged on its smooth-input open. Pulling
this exact statement back to the original finite edge shows that the
constructed edge accounts for its entire graph preimage, even after adic
base change. No density across the omitted original node is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "V" => completeIdentityActionSmoothOpen K n h
local notation "W" => completeIdentityActionGraphSmoothOpen K n h
local notation "p" => completeIdentityActionGraphProjection K n h
local notation "u" => completeIdentityActionSmoothToGraph K n h

/-- The actual smooth graph square is Cartesian over the entire smooth-input open. -/
theorem completeIdentityActionSmoothGraph_isPullback :
    IsPullback (u) (𝟙 (V).toScheme) (p) (V).ι := by
  apply (isPullback_morphismRestrict (p) (V)).flip.of_iso
    (completeIdentityActionGraphSmoothIso K n h) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    change (W).ι = ((p) ∣_ (V)) ≫ (u)
    rw [← completeIdentityActionGraphSmoothSection_inclusion, ← Category.assoc,
      completeIdentityActionGraphSmoothSection_retraction, Category.id_comp]
  · rfl
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- Every specified smooth-input family is its entire complete-graph preimage. -/
theorem completeIdentityActionSmoothFamily_isPullback {T : Scheme}
    (a : T ⟶ (V).toScheme) :
    IsPullback (a ≫ (u)) (𝟙 T) (p) (a ≫ (V).ι) :=
  (IsPullback.of_id_snd (f := a)).paste_horiz
    (completeIdentityActionSmoothGraph_isPullback K n h)

variable (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "j" => edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (0 : Fin n)
local notation "f" => completeIdentityFiniteInput K n h (0 : Fin n) m
local notation "o" => completeIdentityActionInputStageOriginalIso K n h m
local notation "v" => completeIdentityFiniteEdgeToAdicGraph K n h m
local notation "q" => completeIdentityActionGraphStageProjection K n h m

/-- No extra complete-graph points or nilpotents occur over the original finite outgoing edge. -/
theorem completeIdentityFiniteEdgeToGraph_isPullback :
    IsPullback (completeIdentityFiniteEdgeToGraph K n h m) (𝟙 _) (p) ((j) ≫ (f)) := by
  have H := completeIdentityActionSmoothFamily_isPullback K n h
    (completeIdentityFiniteEdgeToUnchanged K n h m ≫
      completeIdentityActionUnchangedToSmooth K n h)
  simpa only [completeIdentityFiniteEdgeToGraph, Category.assoc,
    completeIdentityActionUnchangedToSmooth_inclusion,
    completeIdentityFiniteEdgeToUnchanged_input] using H

/-- The literal adic graph has exactly the same full preimage over that finite edge. -/
theorem completeIdentityFiniteEdgeToAdicGraph_isPullback :
    IsPullback (v) (𝟙 _) (q) ((j) ≫ (o).hom) := by
  have H : IsPullback ((v) ≫ completeIdentityActionGraphStageInclusion K n h m) (𝟙 _)
      (p) (((j) ≫ (o).hom) ≫ completeIdentityActionInputStageInclusion K n h m) := by
    rw [completeIdentityFiniteEdgeToAdicGraph_complete, Category.assoc,
      completeIdentityActionInputStageOriginalIso_inclusion]
    exact completeIdentityFiniteEdgeToGraph_isPullback K n h m
  apply H.of_right _ (IsPullback.of_hasPullback (p) _)
  simp only [completeIdentityFiniteEdgeToAdicGraph, pullback.lift_snd, Category.id_comp]

/-- The actual finite edge is an open subscheme of the whole literal adic graph. -/
instance completeIdentityFiniteEdgeToAdicGraph_open : IsOpenImmersion (v) :=
  MorphismProperty.of_isPullback
    (completeIdentityFiniteEdgeToAdicGraph_isPullback K n h m).flip inferInstance

/-- Every adic-graph family over this original edge is its specified original edge lift. -/
theorem completeIdentityFiniteEdgeToAdicGraph_unique {T : Scheme}
    (g : T ⟶ completeIdentityActionGraphStage K n h m)
    (a : T ⟶ PolygonSmoothing.branchTorus (A)[T;T⁻¹])
    (he : g ≫ (q) = a ≫ (j) ≫ (o).hom) : g = a ≫ (v) := by
  have H := completeIdentityFiniteEdgeToAdicGraph_isPullback K n h m
  have hs := H.lift_snd g a he
  rw [Category.comp_id] at hs
  rw [← hs]
  exact (H.lift_fst g a he).symm

end FLT.Mazur.PolygonInfinitesimalStages
