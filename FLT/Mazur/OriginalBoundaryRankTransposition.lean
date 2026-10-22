/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDoubleRankResidualCorrections
public import FLT.Mazur.RelativeDoubleRankTransposeScalars
public import FLT.Mazur.SchemeScalarKernelPairSymmetry

/-!
# Transposition on the original boundary rank charts

The endpoint exchange of the unchanged original scalar kernel pair constructs
an isomorphism of full independent rank charts. It fixes original scalars, so
exact kernels and residual corrections transfer with both orders exchanged.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData)
local instance transposeOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance transposeOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))
local notation "τ" => (pullbackSymmetry f f).hom
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J

/-- The constructed full chart isomorphism exchanges both original ranks and orders. -/
def originalBoundaryDoubleRankTransposeIso (n m r s : ℕ) :
    doubleRankThickening (Over.mk p) x y n m r s ≅
      doubleRankThickening (Over.mk p) x y m n s r :=
  doubleRankTransposeIso (Over.mk p) x y τ
    (pullbackSymmetry_hom_comp_fst_assoc _ _ _) (pullbackSymmetry_hom_comp_snd_assoc _ _ _)
    n m r s (by
      apply pullback.hom_ext <;>
        simp only [Category.assoc, pullbackSymmetry_hom_comp_fst,
          pullbackSymmetry_hom_comp_snd, Category.id_comp])

/-- Original scalar equations agree exactly after transposing full rank charts. -/
theorem originalBoundary_doubleRank_kernel_transpose (n m r s : ℕ) :
    doubleRankScalarKernel (Over.mk p) x y σ n m r s =
      doubleRankScalarKernel (Over.mk p) x y σ m n s r :=
  doubleRankScalarKernel_transpose (Over.mk p) x y τ
    (pullbackSymmetry_hom_comp_fst_assoc _ _ _) (pullbackSymmetry_hom_comp_snd_assoc _ _ _)
    σ (scalarKernelPair_transpose_scalars _) n m r s

/-- Transposition preserves both original bad closures in the exact residual correction sum. -/
theorem originalBoundary_doubleRank_residual_transpose (n m r s : ℕ) :
    doubleRankScalarKernel (Over.mk p) x y σ n m r s ⊔ H =
      doubleRankScalarKernel (Over.mk p) x y σ m n s r ⊔ H := by
  rw [originalBoundary_doubleRank_kernel_transpose J]

/-- The identical original residual scalar corrects the transposed full coefficient equation. -/
theorem originalBoundary_doubleRank_correction_transpose (n m r s : ℕ) (a b : R) :
    (doubleRankMap (Over.mk p) x y n m r s).appTop (σ a) =
        (doubleRankMap (Over.mk p) x y n m r s).appTop (σ b) ↔
      (doubleRankMap (Over.mk p) x y m n s r).appTop (σ a) =
        (doubleRankMap (Over.mk p) x y m n s r).appTop (σ b) :=
  doubleRankTranspose_correction_iff (Over.mk p) x y τ
    (pullbackSymmetry_hom_comp_fst_assoc _ _ _) (pullbackSymmetry_hom_comp_snd_assoc _ _ _)
    σ (scalarKernelPair_transpose_scalars _) n m r s a b

end FLT.Mazur.EquivalenceRelationOrderedFrames
