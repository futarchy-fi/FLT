/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedChainOverlapEdges
public import FLT.Mazur.PolygonCollapsedChainRetainedComplement

/-!
# Full Laurent covers of distinct chain-chart overlaps

The original polygon detects both possible cyclic edges. The retained edge
is excluded by the full chain ideal, and the omitted edges cover the overlap.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedChainOverlapCover
open PolygonCyclicAtlas PolygonCollapsedChainModel PolygonCollapsedChainOpenCover
open PolygonCollapsedChainCartesianAtlas PolygonCollapsedChainOverlapEdges
open PolygonCollapsedChainRetainedComplement
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)

instance nodeInclusion_isClosedImmersion (a : ChartIndex n i) :
    IsClosedImmersion (nodeInclusion K n i a) := by
  rcases a with b | j
  · cases b <;> dsimp [nodeInclusion] <;> infer_instance
  · dsimp [nodeInclusion]
    infer_instance

/-- A first-edge point lifts uniquely to the actual Cartesian intersection. -/
theorem forward_point (a b : ChartIndex n i) (ha : nodeIndex n i a ≠ i)
    (hab : (finRotate n).symm (nodeIndex n i a) = nodeIndex n i b)
    (x : ↥(pullback (chartMap K n h i a) (chartMap K n h i b)))
    (z : ProjectiveLine.overlap K)
    (hz : PolygonNodeBranches.left K z = nodeInclusion K n i a
      (pullback.fst (chartMap K n h i a) (chartMap K n h i b) x)) :
    forward K n h i a b ha hab z = x := by
  apply (pullback.fst (chartMap K n h i a) (chartMap K n h i b)).isOpenEmbedding.injective
  apply (nodeInclusion K n i a).isEmbedding.injective
  change (forward K n h i a b ha hab ≫ pullback.fst _ _ ≫ nodeInclusion K n i a) z = _
  rw [forward_fst_assoc, firstEdge_nodeInclusion]
  exact hz

/-- The reverse edge is recovered from the second open chart projection. -/
theorem reverse_point (a b : ChartIndex n i) (hb : nodeIndex n i b ≠ i)
    (hba : (finRotate n).symm (nodeIndex n i b) = nodeIndex n i a)
    (x : ↥(pullback (chartMap K n h i a) (chartMap K n h i b)))
    (z : ProjectiveLine.overlap K)
    (hz : PolygonNodeBranches.left K z = nodeInclusion K n i b
      (pullback.snd (chartMap K n h i a) (chartMap K n h i b) x)) :
    reverse K n h i a b hb hba z = x := by
  apply (pullback.snd (chartMap K n h i a) (chartMap K n h i b)).isOpenEmbedding.injective
  apply (nodeInclusion K n i b).isEmbedding.injective
  change (reverse K n h i a b hb hba ≫ pullback.snd _ _ ≫ nodeInclusion K n i b) z = _
  rw [reverse_snd_assoc, firstEdge_nodeInclusion]
  exact hz

/-- Both cyclic orientations together cover the entire distinct-chart intersection. -/
theorem covers (a b : ChartIndex n i) (hne : a ≠ b)
    (x : ↥(pullback (chartMap K n h i a) (chartMap K n h i b))) :
    (∃ ha hab z, forward K n h i a b ha hab z = x) ∨
      (∃ hb hba z, reverse K n h i a b hb hba z = x) := by
  have he : chart K n h (nodeIndex n i a)
      (nodeInclusion K n i a
        (pullback.fst (chartMap K n h i a) (chartMap K n h i b) x)) =
      chart K n h (nodeIndex n i b) (nodeInclusion K n i b
        (pullback.snd (chartMap K n h i a) (chartMap K n h i b) x)) := by
    change (pullback.fst _ _ ≫ nodeInclusion K n i a ≫ chart K n h _) x =
      (pullback.snd _ _ ≫ nodeInclusion K n i b ≫ chart K n h _) x
    rw [← chartMap_ι, ← chartMap_ι, pullback.condition_assoc]
  have hn : nodeIndex n i a ≠ nodeIndex n i b :=
    fun he ↦ hne (nodeIndex_injective n h i he)
  rcases (charts_eq_iff K n h hn _ _).mp he with ⟨z, hab, hz, _⟩ | ⟨z, hba, _, hz⟩
  · have ha := left_incidence_omitted K n h i a
      (pullback.fst (chartMap K n h i a) (chartMap K n h i b) x) z hz
    exact Or.inl ⟨ha, hab, z, forward_point K n h i a b ha hab x z hz⟩
  · have hb := left_incidence_omitted K n h i b
      (pullback.snd (chartMap K n h i a) (chartMap K n h i b) x) z hz
    exact Or.inr ⟨hb, hba, z, reverse_point K n h i a b hb hba x z hz⟩

/-- Possible forward and reverse incidences, with retained edges already excluded. -/
abbrev EdgeIndex (a b : ChartIndex n i) :=
  {_ha : nodeIndex n i a ≠ i // (finRotate n).symm (nodeIndex n i a) = nodeIndex n i b} ⊕
    {_hb : nodeIndex n i b ≠ i // (finRotate n).symm (nodeIndex n i b) = nodeIndex n i a}

/-- The actual map for each surviving oriented edge. -/
def edgeMap (a b : ChartIndex n i) : EdgeIndex n i a b →
    (ProjectiveLine.overlap K ⟶ pullback (chartMap K n h i a) (chartMap K n h i b))
  | .inl e => forward K n h i a b e.val e.property
  | .inr e => reverse K n h i a b e.val e.property

instance edgeMap_isOpenImmersion (a b : ChartIndex n i) (e : EdgeIndex n i a b) :
    IsOpenImmersion (edgeMap K n h i a b e) := by
  cases e <;> dsimp [edgeMap] <;> infer_instance

/-- The full intersection is covered by its actual omitted Laurent edges. -/
def cover (a b : ChartIndex n i) (hne : a ≠ b) :
    (pullback (chartMap K n h i a) (chartMap K n h i b)).OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) (EdgeIndex n i a b)
    (fun _ ↦ ProjectiveLine.overlap K) (edgeMap K n h i a b)
    (fun x ↦ by
      rcases covers K n h i a b hne x with ⟨ha, hab, z, hz⟩ | ⟨hb, hba, z, hz⟩
      · exact ⟨.inl ⟨ha, hab⟩, z, hz⟩
      · exact ⟨.inr ⟨hb, hba⟩, z, hz⟩)
    (fun _ ↦ inferInstance)

end FLT.Mazur.PolygonCollapsedChainOverlapCover
