/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFiniteComparisonTests
public import FLT.Mazur.RelativeRankThickeningFinite

/-!
# Finite full original comparisons on actual rank thickenings

Every coefficient test has an unsplit rank thickening at every order. Its
entire first endpoint pullback is finite by complete-frame descent. This
constructs finite closed comparison tests even at residual nonfinite points;
no finite endpoint is assumed and no flat rank-stage cover is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local instance stageComparisonOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance stageComparisonOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance stageComparisonOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance stageComparisonOver_quasiFinite : LocallyQuasiFinite (Over.mk p).hom :=
  ‹LocallyQuasiFinite p›
local instance stageComparisonBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
attribute [local irreducible] scalarMorphism

omit [IsAffine A] in
/-- The whole first endpoint is finite on every original coefficient rank thickening. -/
theorem originalBoundary_rankStage_endpoint_finite
    (t : B ⟶ pullback f f) (n k : ℕ) :
    IsFinite (pullback.snd p
      ((rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ≫ x)) := by
  rw [Category.assoc]
  exact finite_pullback_rankPullback (Over.mk p) (t ≫ x) n k

/-- The actual full comparison is finite on each unsplit infinitesimal rank test. -/
theorem originalBoundary_rankStage_comparison_finite
    (t : B ⟶ pullback f f) (n k : ℕ) :
    IsFinite (pullback.snd c (rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t)) := by
  let _ := originalBoundary_rankStage_endpoint_finite J t n k
  exact originalBoundary_comparison_test_finite J hJ _

/-- The unchanged full relation cuts out a closed subscheme of the entire rank stage. -/
theorem originalBoundary_rankStage_comparison_closedImmersion
    (e : CategoryTheory.EquivalenceRelation p q) (t : B ⟶ pullback f f) (n k : ℕ) :
    IsClosedImmersion (pullback.snd c
      (rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t)) := by
  let _ := originalBoundary_rankStage_endpoint_finite J t n k
  exact originalBoundary_comparison_test_closedImmersion J hJ _ e

/-- Original comparison membership is specialization-closed inside every full rank stage. -/
theorem originalBoundary_rankStage_comparison_specializes
    (t : B ⟶ pullback f f) (n k : ℕ)
    {u v : rankPullbackThickening (Over.mk p) (t ≫ x) n k} (huv : u ⤳ v)
    (hu : t (rankPullbackMap (Over.mk p) (t ≫ x) n k u) ∈ Set.range c) :
    t (rankPullbackMap (Over.mk p) (t ≫ x) n k v) ∈ Set.range c := by
  let _ := originalBoundary_rankStage_endpoint_finite J t n k
  exact originalBoundary_comparison_test_specializes J hJ
    (rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) huv hu

end FLT.Mazur.EquivalenceRelationOrderedFrames
