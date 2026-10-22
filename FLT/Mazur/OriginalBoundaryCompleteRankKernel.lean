/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDoubleRankResidualCorrections
public import FLT.Mazur.RelativeDoubleRankCompleteKernel

/-!
# Complete rank equations recover the original boundary scalar kernel

The diagonal section of the original scalar kernel pair detects its original
boundary scalar kernel exactly. The full finite rank rectangle therefore has
that kernel's radical, uniformly in both orders. Equal-rank charts are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem scalar_kernel_of_retraction {X Y : Scheme.{0}}
    (l : Y ⟶ X) (d : X ⟶ Y) (hd : d ≫ l = 𝟙 X)
    {R : Type} [CommRing R] (σ : R →+* Γ(X, ⊤)) :
    RingHom.ker (l.appTop.hom.comp σ) = RingHom.ker σ := by
  ext a
  constructor
  · intro ha
    have hz := congrArg d.appTop ha
    change (l.appTop ≫ d.appTop) (σ a) = d.appTop 0 at hz
    rw [← Scheme.Hom.comp_appTop, hd, Scheme.Hom.id_appTop, map_zero] at hz
    exact hz
  · intro ha
    change l.appTop (σ a) = 0
    rw [show σ a = 0 from ha, map_zero]

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData)
local instance completeKernelOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance completeKernelOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))

/-- The full rectangle's original scalar equations, including its equal-rank charts. -/
def originalBoundaryCompleteRankKernel (N r s : ℕ) : Ideal R :=
  doubleRankCompleteKernel (Over.mk p) x y σ N r s

omit [IsSeparated p] [Etale p] in
/-- The diagonal retraction identifies the kernel-pair scalar kernel exactly. -/
theorem originalBoundary_pair_scalar_kernel :
    RingHom.ker σ = originalBoundaryScalarKernel (p := p) (q := q) J := by
  exact scalar_kernel_of_retraction (pullback.fst f f) (pullback.diagonal f)
    (pullback.diagonal_fst f) (algebraMap R Γ(J.subscheme, ⊤))

/-- Membership is equality on every full chart, with no condition excluding equal ranks. -/
theorem mem_originalBoundaryCompleteRankKernel (N r s : ℕ) (a : R) :
    a ∈ originalBoundaryCompleteRankKernel (p := p) (q := q) J N r s ↔
      ∀ n m : Fin (N + 1),
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ a) = 0 :=
  mem_doubleRankCompleteKernel (Over.mk p) x y σ N r s a

variable [IsAffine A] [TopologicalSpace.NoetherianSpace A] [QuasiCompact p]
local instance completeKernelOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance completeKernelBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι

/-- The same complete rectangle recovers the full boundary kernel radical at every order. -/
theorem exists_originalBoundary_complete_rank_kernel :
    ∃ N : ℕ, ∀ r s : ℕ,
      (originalBoundaryCompleteRankKernel (p := p) (q := q) J N r s).radical =
        (originalBoundaryScalarKernel (p := p) (q := q) J).radical := by
  obtain ⟨N, hN⟩ := exists_uniform_doubleRank_complete_kernel (Over.mk p) x y σ
  exact ⟨N, fun r s ↦ (hN r s).trans
    (congrArg Ideal.radical (originalBoundary_pair_scalar_kernel J))⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
