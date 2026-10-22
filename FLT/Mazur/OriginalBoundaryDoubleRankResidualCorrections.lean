/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryResidualDoubleRankEquations
public import FLT.Mazur.RelativeDoubleRankResidualCorrections

/-!
# Original scalar corrections on the residual independent rank charts

The residual ideal and both original bad closures stay fixed. Full boundary
kernel elements already vanish on every chart. Independent chart corrections
can therefore be combined in the original scalar ring, with an explicit power.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData)
local instance residualCorrectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance residualCorrectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J

/-- Original boundary equations vanish on every entire rank chart, including nilpotents. -/
theorem originalBoundaryScalarKernel_le_doubleRankScalarKernel (n m r s : ℕ) :
    originalBoundaryScalarKernel (p := p) (q := q) J ≤
      doubleRankScalarKernel (Over.mk p) x y σ n m r s := by
  intro a ha
  have hz : algebraMap R Γ(J.subscheme, ⊤) a = 0 :=
    (mem_originalBoundaryScalarKernel J a).mp ha
  have hfst : (pullback.fst f f).appTop (algebraMap R Γ(J.subscheme, ⊤) a) = 0 :=
    (congrArg (pullback.fst f f).appTop hz).trans (map_zero _)
  exact (congrArg (doubleRankMap (Over.mk p) x y n m r s).appTop hfst).trans (map_zero _)

/-- The exact finite collision kernel already contains the full original boundary kernel. -/
theorem originalBoundaryScalarKernel_le_doubleRankKernel (N r s : ℕ) :
    originalBoundaryScalarKernel (p := p) (q := q) J ≤
      originalBoundaryDoubleRankKernel (p := p) (q := q) J N r s := by
  intro a ha
  apply (mem_originalBoundaryDoubleRankKernel J N r s a).mpr
  intro n m _
  exact originalBoundaryScalarKernel_le_doubleRankScalarKernel J n.val m.val r s ha

/-- Membership means one original residual scalar corrects every full off-diagonal equation. -/
theorem mem_originalBoundaryResidualDoubleRankIdeal (N r s : ℕ) (a : R) :
    a ∈ originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s ↔
      ∃ b ∈ H, ∀ n m : Fin (N + 1), n.val ≠ m.val →
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ a) =
          (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ b) :=
  mem_doubleRank_kernel_sup_iff (Over.mk p) x y σ N r s H a

/-- Independent original residual chart corrections yield an exact shared power containment. -/
theorem originalBoundary_doubleRank_residual_power_le (N r s : ℕ) (Q : Ideal R) (k : ℕ)
    (h : ∀ n m : Fin (N + 1), n.val ≠ m.val →
      Q ^ k ≤ doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H) :
    Q ^ (Nat.card (doubleRankOffDiagonal N) * k) ≤
      originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s :=
  doubleRank_residual_power_le (Over.mk p) x y σ N r s H Q k h

/-- Chartwise radical containments suffice when the original target ideal is finitely generated. -/
theorem exists_originalBoundary_doubleRank_residual_power (N r s : ℕ) (Q : Ideal R)
    (hfg : Q.FG) (h : ∀ n m : Fin (N + 1), n.val ≠ m.val →
      Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r s ⊔ H).radical) :
    ∃ k : ℕ, Q ^ k ≤
      originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s :=
  exists_doubleRank_residual_power (Over.mk p) x y σ N r s H Q hfg h

end FLT.Mazur.EquivalenceRelationOrderedFrames
