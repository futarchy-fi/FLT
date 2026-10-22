/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDoubleRankTests
public import FLT.Mazur.RelativeDoubleRankExactDenominators

/-!
# Exact original boundary scalar kernels on independent ranks

All scalar equations are computed in the unchanged original invariant ring.
At prescribed independent orders a finite intersection of full chart kernels
has radical exactly the original rank-collision ideal. No original scalar
extension, source finiteness over that ring, or stage arrow is presumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (J : A.IdealSheafData)
local instance scalarKernelOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarKernelOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarKernelOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))

/-- The exact original scalar equations on a finite rectangle of full off-diagonal stages. -/
def originalBoundaryDoubleRankKernel (N r s : ℕ) : Ideal R :=
  doubleRankCollisionKernel (Over.mk p) x y σ N r s

omit [QuasiCompact p] in
/-- Every equation is an equation of full global sections on the original rank thickening. -/
theorem mem_originalBoundaryDoubleRankKernel (N r s : ℕ) (a : R) :
    a ∈ originalBoundaryDoubleRankKernel (p := p) (q := q) J N r s ↔
      ∀ n m : Fin (N + 1), n.val ≠ m.val →
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ a) = 0 :=
  mem_doubleRankCollisionKernel (Over.mk p) x y σ N r s a

variable [IsAffine A] [TopologicalSpace.NoetherianSpace A]
local instance scalarKernelBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι

/-- Full exact original equations compute the entire rank obstruction at every pair of orders. -/
theorem exists_originalBoundary_rank_kernel_radical (r s : ℕ) :
    ∃ N : ℕ, originalBoundaryRankCollisionIdeal (p := p) (q := q) J =
      (originalBoundaryDoubleRankKernel (p := p) (q := q) J N r s).radical := by
  simpa only [originalBoundaryRankCollisionIdeal, originalBoundaryDoubleRankKernel,
    scalarMorphism_comp] using exists_rankCollisionIdeal_exact_kernel (Over.mk p) x y σ r s

/-- An original collision-free prime supplies an exact scalar equation on every full chart. -/
theorem exists_originalBoundary_rank_exact_denominator (r s : ℕ) (P : PrimeSpectrum R)
    (hP : ¬ originalBoundaryRankCollisionIdeal (p := p) (q := q) J ≤ P.asIdeal) :
    ∃ (N : ℕ) (a : R), a ∉ P.asIdeal ∧
      a ∈ originalBoundaryDoubleRankKernel (p := p) (q := q) J N r s ∧
      a ∈ originalBoundaryRankCollisionIdeal (p := p) (q := q) J := by
  have h : ¬ rankCollisionIdeal (Over.mk p) x y (scalarMorphism σ) ≤ P.asIdeal := by
    simpa only [originalBoundaryRankCollisionIdeal, scalarMorphism_comp] using hP
  simpa only [originalBoundaryRankCollisionIdeal, originalBoundaryDoubleRankKernel,
    scalarMorphism_comp] using exists_doubleRank_exact_denominator (Over.mk p) x y σ r s P h

end FLT.Mazur.EquivalenceRelationOrderedFrames
