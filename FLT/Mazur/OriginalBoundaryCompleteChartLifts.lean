/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryCompleteRankLift

/-!
# Full lifts from independent corrections on every rank chart

Independent residual corrections on the complete finite rectangle combine
in the original scalar ring. A power of the whole finitely generated scalar
ideal then lifts on the entire original boundary. The chart containments are
explicit inputs; scalar endpoint equality alone does not supply them.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A}
  [IsSeparated p] [Etale p] [QuasiCompact p] [IsAffine A]
  [TopologicalSpace.NoetherianSpace A]
  (J : A.IdealSheafData) (e : CategoryTheory.EquivalenceRelation p q)
  (hJ : J.comap p = J.comap q)
  [IsAffine S] (g : A ⟶ S) (hg : p ≫ g = q ≫ g) [IsSeparated g]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local instance completeLiftOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance completeLiftOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J
local notation "L" => originalBoundaryLiftIdeal (p := p) (q := q) J t.val

include e hg in
/-- Independent full-chart corrections yield a uniform ideal power of actual original lifts. -/
theorem exists_originalBoundary_complete_chart_ideal_lifts :
    ∃ N : ℕ, ∀ (r s : ℕ) (Q : Ideal R) (_ : Q.FG),
      (∀ n m : Fin (N + 1),
        Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H).radical) →
      ∃ k : ℕ, Q ^ k ≤ L := by
  obtain ⟨N, hN⟩ := exists_originalBoundary_complete_rank_ideal_lifts J e hJ g hg t
  refine ⟨N, fun r s Q hfg h ↦ ?_⟩
  apply hN r s Q hfg
  obtain ⟨d, hd⟩ := FiniteScalarResidualCorrections.exists_pow_le_shared_kernel
    (fun i : Fin (N + 1) × Fin (N + 1) ↦
      (doubleRankMap (Over.mk p) x y i.1.val i.2.val r s).appTop.hom.comp σ)
    H Q hfg (fun i ↦ h i.1 i.2)
  change Q ^ d ≤ originalBoundaryCompleteResidualIdeal (p := p) (q := q) J N r s at hd
  intro a ha
  exact ⟨d, hd (Ideal.pow_mem_pow ha d)⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
