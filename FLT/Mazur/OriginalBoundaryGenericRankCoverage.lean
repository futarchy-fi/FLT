/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryLocalImageKernelDetection

/-!
# Generic component tests for full original rank coverage

Only the generic points of actual rank-stage components need comparison
arrows. Finiteness of the entire rank-stage comparison extends coverage to
all coefficient points. Pointwise unramified neighborhoods then detect all
nonreduced equations. Generic coverage remains an explicit geometric input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem dense_of_generic_points {X : Scheme.{0}} {s : Set X}
    (h : genericPoints X ⊆ s) : Dense s := by
  have hd : Dense (genericPoints X) := by
    rw [dense_iff_closure_eq, genericPoints.closure]
  exact hd.mono h

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local instance genericRankOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance genericRankOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance genericRankOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance genericRankBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
attribute [local irreducible] scalarMorphism

/-- Generic component points at a single rank order cover the whole original coefficient test. -/
theorem originalBoundary_coverage_of_generic_rankStages
    (t : B ⟶ pullback f f) (k : ℕ)
    (h : ∀ n, genericPoints (rankPullbackThickening (Over.mk p) (t ≫ x) n k) ⊆
      (rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ⁻¹' Set.range c) :
    Set.range t ⊆ Set.range c :=
  originalBoundary_coverage_of_dense_rankStages J hJ t k
    (fun n ↦ dense_of_generic_points (h n))

/-- Generic component coverage and local image rigidity kill all full original equations. -/
theorem originalBoundary_kernel_of_generic_rankStages [IsLocallyNoetherian B]
    (e : CategoryTheory.EquivalenceRelation p q) (t : B ⟶ pullback f f) (k : ℕ)
    (h : ∀ n, genericPoints (rankPullbackThickening (Over.mk p) (t ≫ x) n k) ⊆
      (rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ⁻¹' Set.range c)
    (hU : ∀ u : B, ∃ U : J.subscheme.Opens,
      (t ≫ pullback.snd f f) u ∈ U ∧ FormallyUnramified (U.ι ≫ projection f)) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom :=
  originalBoundary_kernel_zero_of_local_image_coverage e J hJ t hU
    (originalBoundary_coverage_of_generic_rankStages J hJ t k h)

end FLT.Mazur.EquivalenceRelationOrderedFrames
