/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFrameRebaseGeometric
public import FLT.Mazur.RelativeFrameSpecializationCeiling

/-!
# Original ranks and their local ceilings are invariant under the full relation

Rebasing an entire geometric enumeration identifies all original rank images.
Openness of both endpoints also identifies the closures of those images.
Thus the local ceiling is unchanged along every original relation arrow,
including on the lower-rank residual locus.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q)
local instance rankSaturationOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankSaturationOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankSaturationOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

include e in
/-- Every original frame rank is preserved at both endpoints of an arbitrary original arrow. -/
theorem rankImage_endpoint_iff (n : ℕ) (x : D) :
    p x ∈ rankImageOpen (Over.mk p) n ↔ q x ∈ rankImageOpen (Over.mk p) n := by
  let K := AlgebraicClosure (D.residueField x)
  let a := Spec.map (CommRingCat.ofHom (algebraMap (D.residueField x) K)) ≫
    D.fromSpecResidueField x
  obtain ⟨m, t, ht⟩ := exists_complete_geometric_tuple (Over.mk p) (a ≫ p)
  have hp := geometric_mem_rankImage_iff (Over.mk p) t ht n
  have hq := geometric_mem_rankImage_iff (Over.mk p) (rebaseFrame e (Fin m) a t)
    (rebaseFrame_complete e (Fin m) a t ht) n
  have h := hp.trans hq.symm
  have ha : a default = x := D.fromSpecResidueField_apply x _
  change p (a default) ∈ rankImageOpen (Over.mk p) n ↔
    q (a default) ∈ rankImageOpen (Over.mk p) n at h
  rwa [ha] at h

include e in
/-- Original rank-image opens are saturated under the entire original relation. -/
theorem rankImage_preimage_eq (n : ℕ) :
    p ⁻¹ᵁ rankImageOpen (Over.mk p) n = q ⁻¹ᵁ rankImageOpen (Over.mk p) n := by
  ext x
  exact rankImage_endpoint_iff e n x

include e in
/-- The exact closed rank bounds, including all residual points, are saturated. -/
theorem rankAtMost_endpoint_iff (n : ℕ) (x : D) :
    p x ∈ rankAtMost (Over.mk p) n ↔ q x ∈ rankAtMost (Over.mk p) n :=
  not_congr (rankImage_endpoint_iff e (n + 1) x)

include e in
/-- The locally closed exact rank pieces agree along all original arrows. -/
theorem exactRank_endpoint_iff (n : ℕ) (x : D) :
    p x ∈ exactRank (Over.mk p) n ↔ q x ∈ exactRank (Over.mk p) n :=
  and_congr (rankImage_endpoint_iff e n x) (rankAtMost_endpoint_iff e n x)

variable [Etale q]

include e in
/-- Openness of the endpoints makes exclusion of approaching larger frames invariant too. -/
theorem rankBound_preimage_eq (n : ℕ) :
    p ⁻¹ᵁ rankBoundOpen (Over.mk p) n = q ⁻¹ᵁ rankBoundOpen (Over.mk p) n := by
  have hi : p ⁻¹' (rankImageOpen (Over.mk p) (n + 1) : Set A) =
      q ⁻¹' (rankImageOpen (Over.mk p) (n + 1) : Set A) :=
    congrArg (fun U : D.Opens ↦ (U : Set D)) (rankImage_preimage_eq e (n + 1))
  apply TopologicalSpace.Opens.ext
  change p ⁻¹' (closure (rankImageOpen (Over.mk p) (n + 1) : Set A))ᶜ =
    q ⁻¹' (closure (rankImageOpen (Over.mk p) (n + 1) : Set A))ᶜ
  rw [Set.preimage_compl, Set.preimage_compl,
    p.isOpenMap.preimage_closure_eq_closure_preimage p.continuous,
    q.isOpenMap.preimage_closure_eq_closure_preimage q.continuous, hi]

variable [NoetherianSpace A]

include e in
/-- The least original local rank ceiling is constant on the full equivalence relation. -/
theorem specializationRankCeiling_endpoints (x : D) :
    specializationRankCeiling (Over.mk p) (p x) =
      specializationRankCeiling (Over.mk p) (q x) := by
  have h (n : ℕ) : specializationRankCeiling (Over.mk p) (p x) ≤ n ↔
      specializationRankCeiling (Over.mk p) (q x) ≤ n := by
    rw [← mem_rankBound_iff_specializationRankCeiling,
      ← mem_rankBound_iff_specializationRankCeiling]
    exact (congrArg (fun U : D.Opens ↦ x ∈ U) (rankBound_preimage_eq e n)).to_iff
  exact Nat.le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)

end FLT.Mazur.EquivalenceRelationOrderedFrames
