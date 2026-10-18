/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteClosedLocus
public import FLT.Mazur.RelativeFrameClosedRankCompleteness

/-!
# Exact original rank detects normalized completeness

A normalized n-frame is complete precisely when its original endpoint has no
(n+1)-frame. The criterion uses the entire original first projection and works
at all residue fields, including points on closed rank strata.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (n : ℕ) (o : Fin n)
local instance exactRankOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance exactRankOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance exactRankOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

/-- Completeness is exactly the original closed rank bound at the unchanged endpoint. -/
theorem complete_iff_endpoint_rankAtMost {K : Type} [Field K]
    (u : Spec (.of K) ⟶ source p q (Fin n) o) :
    Complete (Fin n) o u ↔
      first p q (Fin n) o (u default) ∈ rankAtMost (Over.mk p) n := by
  constructor
  · intro hc
    let g := Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))
    have hc' := complete_scalar (Fin n) o u g hc
    have h := geometric_mem_rankImage_iff (Over.mk p)
      (testFrame (Fin n) o (g ≫ u)) hc' (n + 1)
    have hg : g default = (default : Spec (.of K)) := Subsingleton.elim _ _
    change first p q (Fin n) o (u (g default)) ∈
      rankImageOpen (Over.mk p) (n + 1) ↔ n + 1 ≤ n at h
    rw [hg] at h
    exact fun hx ↦ Nat.not_succ_le_self n (h.mp hx)
  · intro hx
    exact geometric_complete_of_rankAtMost (Over.mk p) n (testFrame (Fin n) o u) hx

/-- The whole normalized complete locus is the inverse image of the original closed rank set. -/
theorem completePointLocus_eq_rankAtMost_preimage :
    completePointLocus (p := p) (q := q) (Fin n) o =
      first p q (Fin n) o ⁻¹' rankAtMost (Over.mk p) n := by
  ext x
  have h := complete_iff_endpoint_rankAtMost n o
    ((source p q (Fin n) o).fromSpecResidueField x)
  have hx : (source p q (Fin n) o).fromSpecResidueField x default = x :=
    Scheme.fromSpecResidueField_apply x default
  change Complete (Fin n) o ((source p q (Fin n) o).fromSpecResidueField x) ↔ _
  exact h.trans (congrArg (fun y ↦ first p q (Fin n) o y ∈
    rankAtMost (Over.mk p) n) hx).to_iff

/-- Incomplete normalized frames are precisely the endpoints admitting a larger original frame. -/
theorem not_completePoint_iff_larger_frame (x : source p q (Fin n) o) :
    x ∉ completePointLocus (p := p) (q := q) (Fin n) o ↔
      ∃ y : (distinctScheme (Over.mk p) (Fin (n + 1))).left,
        (distinctScheme (Over.mk p) (Fin (n + 1))).hom y = first p q (Fin n) o x := by
  rw [completePointLocus_eq_rankAtMost_preimage]
  change ¬ ¬ _ ↔ _
  exact not_not

/-- One uniform original rank bound makes every sufficiently large normalized frame complete. -/
theorem exists_eventually_complete_frames [TopologicalSpace.NoetherianSpace A] :
    ∃ N : ℕ, ∀ (m : ℕ) (j : Fin m), N ≤ m →
      completePointLocus (p := p) (q := q) (Fin m) j = Set.univ := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound (Over.mk p)
  refine ⟨N, fun m j hm ↦ Set.eq_univ_of_forall fun x ↦ ?_⟩
  rw [completePointLocus_eq_rankAtMost_preimage]
  intro hx
  exact Nat.not_succ_le_self m ((hN _ (m + 1) hx).trans hm)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
