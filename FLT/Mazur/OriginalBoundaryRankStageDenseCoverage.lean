/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankStageComparison
public import FLT.Mazur.SchemeFiniteComparisonDenseTests

/-!
# Dense original comparison coverage on full rank stages

Constructed finiteness turns dense actual image coverage on each rank piece
into coverage of the whole coefficient test. The stage order can be fixed
for this pointwise conclusion. Reduced stages have unique full arrows;
nonreduced stages retain a possibly nonzero nilpotent comparison obstruction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeFiniteEndpointComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [Etale p] [IsSeparated p] [QuasiCompact p] [LocallyQuasiFinite p]
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local instance denseStageOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance denseStageOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance denseStageOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance denseStageBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
attribute [local irreducible] scalarMorphism

/-- Dense actual coverage suffices on each full stage, with no assumed finite endpoint. -/
theorem originalBoundary_rankStage_surjective_of_dense
    (t : B ⟶ pullback f f) (n k : ℕ)
    (h : Dense ((rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ⁻¹' Set.range c)) :
    Surjective (pullback.snd c (rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t)) := by
  let _ := originalBoundary_rankStage_comparison_finite J hJ t n k
  exact comparison_surjective_of_dense c _ h

/-- Dense coverage on all ranks at one order covers every original coefficient point. -/
theorem originalBoundary_coverage_of_dense_rankStages
    (t : B ⟶ pullback f f) (k : ℕ)
    (h : ∀ n, Dense ((rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ⁻¹' Set.range c)) :
    Set.range t ⊆ Set.range c := by
  rintro _ ⟨u, rfl⟩
  obtain ⟨n, v, hv⟩ := exists_rankPullback_lift (Over.mk p) (t ≫ x) k u
  let _ := originalBoundary_rankStage_surjective_of_dense J hJ t n k (h n)
  have hr : v ∈ Set.range
      (pullback.snd c (rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t)) :=
    (pullback.snd c _).surjective v
  rw [Scheme.Pullback.range_snd] at hr
  change t (rankPullbackMap (Over.mk p) (t ≫ x) n k v) ∈ Set.range c at hr
  rwa [hv] at hr

/-- Reduced rank stages have unique full original arrows from dense image coverage. -/
theorem originalBoundary_rankStage_unique_lift_of_dense
    (e : CategoryTheory.EquivalenceRelation p q) (t : B ⟶ pullback f f) (n k : ℕ)
    [IsReduced (rankPullbackThickening (Over.mk p) (t ≫ x) n k)]
    (h : Dense ((rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ⁻¹' Set.range c)) :
    ∃! d : rankPullbackThickening (Over.mk p) (t ≫ x) n k ⟶ pullback p J.subschemeι,
      d ≫ c = rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t := by
  let _ := originalBoundary_rankStage_comparison_finite J hJ t n k
  let _ := originalBoundaryComparison_mono e J hJ
  exact comparison_unique_lift_of_dense c _ h

/-- Dense coverage on a compact nonreduced stage only gives nilpotence of full equations. -/
theorem originalBoundary_rankStage_kernel_nilpotent
    (t : B ⟶ pullback f f) (n k : ℕ)
    [CompactSpace (rankPullbackThickening (Over.mk p) (t ≫ x) n k)]
    (h : Dense ((rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t) ⁻¹' Set.range c))
    (r : Γ(pullback f f, ⊤)) (hr : (c).appTop r = 0) :
    IsNilpotent ((rankPullbackMap (Over.mk p) (t ≫ x) n k ≫ t).appTop r) := by
  let _ := originalBoundary_rankStage_comparison_finite J hJ t n k
  exact comparison_kernel_isNilpotent_of_dense c _ h r hr

end FLT.Mazur.EquivalenceRelationOrderedFrames
