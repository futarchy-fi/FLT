/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXTerminalConicCover
public import FLT.Mazur.PolygonCyclicNormalizationRanges

/-!
# Full affine terminal branches meet the conic in their ordered punctures

Restrict the complete conic boundary to both affine normalization branches.
The original Laurent coordinate is inverted on the terminal side.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk : 2 * (k + 1) ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ (k + 1) * b3) (h4 : W.a₄ = π ^ (k + 1) * b4)
  (h6 : W.a₆ = (π ^ (k + 1)) ^ 2 * b6) (hp : 2 * (k + 1) < n)
local notation "K" => ResidueField R
local notation "W₀" => W.map (residue R)
local notation "c" => residue R b6
local notation "ψ" => residueNodeConicMap D k hk b3 b4 b6 h3 h4 h6 hp
local notation "s" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ψ))
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (k + 1) hp b6 h6)
local notation "s₁" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundaryFirst W₀ c ha hc)))
local notation "s₂" => Spec.map
  (CommRingCat.ofHom (AlgHom.toRingHom (conicBoundarySecond W₀ c ha hc)))
local notation "I" => Scheme.Spec.mapIso
  (Iso.op (RingEquiv.toCommRingCatIso
    (AlgEquiv.toRingEquiv (LaurentPolynomial.invert (R := K)))))

local notation "ι" => Iso.hom I
local notation "p" => ProjectiveLine.overlapLeft K

/-- The first conic puncture is the full intersection with the opposite affine branch. -/
theorem residueNodeConicFirstBranch_isPullback :
    IsPullback s₁ (ι ≫ p) s (PolygonCyclicAtlas.secondBranch K) := by
  have H : (ι ≫ p) ≫ PolygonCyclicAtlas.secondBranch K = s₁ ≫ s := by
    rw [Category.assoc, PolygonCyclicAtlas.overlap_secondBranch]
    exact (residueNodeConicFirst_spec D k hk b3 b4 b6 h3 h4 h6 hp).symm
  apply IsOpenImmersion.isPullback _ _ _ _ H
  apply TopologicalSpace.Opens.ext
  change (PolygonCyclicAtlas.secondBranch K) ⁻¹' Set.range s = Set.range (ι ≫ p)
  ext a
  constructor
  · rintro ⟨z, hz⟩
    have hz' : z ∈ Set.range s₁ ∪ Set.range s₂ := by
      rw [residueNodeConicPunctures_cover D k hk b3 b4 b6 h3 h4 h6 hp]
      trivial
    rcases hz' with hz' | hz'
    · obtain ⟨v, rfl⟩ := hz'
      refine ⟨v, (PolygonCyclicAtlas.secondBranch K).isClosedEmbedding.injective ?_⟩
      exact (congrArg (fun f => f v) H).trans hz
    · obtain ⟨v, rfl⟩ := hz'
      apply False.elim
      apply PolygonCyclicNormalizationRanges.second_not_left K a
      refine ⟨ι v, ?_⟩
      exact (congrArg (fun f => f v)
        (residueNodeConicSecond_spec D k hk b3 b4 b6 h3 h4 h6 hp)).symm.trans hz
  · rintro ⟨v, rfl⟩
    exact ⟨s₁ v, (congrArg (fun f => f v) H).symm⟩

/-- The second conic puncture is the full intersection with the opposite affine branch. -/
theorem residueNodeConicSecondBranch_isPullback :
    IsPullback s₂ (ι ≫ p) s (PolygonCyclicAtlas.firstBranch K) := by
  have H : (ι ≫ p) ≫ PolygonCyclicAtlas.firstBranch K = s₂ ≫ s := by
    rw [Category.assoc, PolygonCyclicAtlas.overlap_firstBranch]
    exact (residueNodeConicSecond_spec D k hk b3 b4 b6 h3 h4 h6 hp).symm
  apply IsOpenImmersion.isPullback _ _ _ _ H
  apply TopologicalSpace.Opens.ext
  change (PolygonCyclicAtlas.firstBranch K) ⁻¹' Set.range s = Set.range (ι ≫ p)
  ext a
  constructor
  · rintro ⟨z, hz⟩
    have hz' : z ∈ Set.range s₁ ∪ Set.range s₂ := by
      rw [residueNodeConicPunctures_cover D k hk b3 b4 b6 h3 h4 h6 hp]
      trivial
    rcases hz' with hz' | hz'
    · obtain ⟨v, rfl⟩ := hz'
      apply False.elim
      apply PolygonCyclicNormalizationRanges.first_not_right K a
      refine ⟨ι v, ?_⟩
      exact (congrArg (fun f => f v)
        (residueNodeConicFirst_spec D k hk b3 b4 b6 h3 h4 h6 hp)).symm.trans hz
    · obtain ⟨v, rfl⟩ := hz'
      refine ⟨v, (PolygonCyclicAtlas.firstBranch K).isClosedEmbedding.injective ?_⟩
      exact (congrArg (fun f => f v) H).trans hz
  · rintro ⟨v, rfl⟩
    exact ⟨s₂ v, (congrArg (fun f => f v) H).symm⟩

end FLT.Mazur.WeierstrassSuccessiveX
