/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonAmbientAffineRelationEtale

/-!
# Exact original relation domains for the affine cover

An original relation arrow belongs to a constructed overlap exactly when
both endpoints belong to the selected original affine opens. Every original
arrow lies in such an overlap. These are the full relation domains, without
an invariance assumption or an identification with a diagonal.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] (d : ℕ) (V : Over (Spec (.of R)))
  {L : X.Modules} (hL : AmpleLineBundle L)
  (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "C" => commonAmbientGrassmannianAffineCover f d V hL
variable (i j : (commonAmbientGrassmannianAffineCover f d V hL).I₀)
local notation "a" => commonAmbientAffineInclusion f d V hL i
local notation "b" => commonAmbientAffineInclusion f d V hL j
local notation "p" => variableChartRelationFst f hL d V c
local notation "q" => variableChartRelationSnd f hL d V c
local notation "o" => commonAmbientAffineRelationOther f d V hL c i

/-- An original arrow lifts to the actual overlap with both original endpoints retained. -/
theorem commonAmbientAffineRelation_original_lift (r : (variableChartRelation f hL d V c).left)
    (x : (commonAmbientAffineTest f d V hL i).left)
    (y : (commonAmbientAffineTest f d V hL j).left)
    (hx : (p).left r = (a).left x) (hy : (q).left r = (b).left y) :
    ∃ z : (commonAmbientAffineRelation f d V hL c i j).left,
      (commonAmbientAffineRelationOriginal f d V hL c i j).left z = r ∧
      (commonAmbientAffineRelationFst f d V hL c i j).left z = x ∧
      (commonAmbientAffineRelationSnd f d V hL c i j).left z = y := by
  obtain ⟨s, hs₁, hs₂⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_hasPullback p a).map (Over.forget _)) r x hx
  have hs : (o).left s = (b).left y := (congrArg (q).left hs₁).trans hy
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.exists_preimage_of_isPullback
    ((IsPullback.of_hasPullback o b).map (Over.forget _)) s y hs
  exact ⟨z, (congrArg (pullback.fst p a).left hz₁).trans hs₁,
    (congrArg (pullback.snd p a).left hz₁).trans hs₂, hz₂⟩

/-- The actual overlap is exactly the two-endpoint inverse-image open in the full relation. -/
theorem commonAmbientAffineRelationOriginal_opensRange :
    (commonAmbientAffineRelationOriginal f d V hL c i j).left.opensRange =
      (p).left ⁻¹ᵁ (a).left.opensRange ⊓ (q).left ⁻¹ᵁ (b).left.opensRange := by
  ext r
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨⟨(commonAmbientAffineRelationFst f d V hL c i j).left z,
      (congrArg (fun k ↦ k.left z)
        (commonAmbientAffineRelationOriginal_fst f d V hL c i j)).symm⟩,
      ⟨(commonAmbientAffineRelationSnd f d V hL c i j).left z,
      (congrArg (fun k ↦ k.left z)
        (commonAmbientAffineRelationOriginal_snd f d V hL c i j)).symm⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    obtain ⟨z, hz, _, _⟩ := commonAmbientAffineRelation_original_lift f d V hL c i j
      r x y hx.symm hy.symm
    exact ⟨z, hz⟩

/-- Every original relation arrow lies in a full overlap of two constructed affine charts. -/
theorem commonAmbientAffineRelation_covers (r : (variableChartRelation f hL d V c).left) :
    ∃ (i j : (commonAmbientGrassmannianAffineCover f d V hL).I₀),
      r ∈ (commonAmbientAffineRelationOriginal f d V hL c i j).left.opensRange := by
  obtain ⟨i, x, hx⟩ := (C).exists_eq ((variableChartRelationFst f hL d V c).left r)
  obtain ⟨j, y, hy⟩ := (C).exists_eq ((variableChartRelationSnd f hL d V c).left r)
  obtain ⟨z, hz, _, _⟩ := commonAmbientAffineRelation_original_lift f d V hL c i j
    r x y hx.symm hy.symm
  exact ⟨i, j, z, hz⟩

end FLT.Mazur.HilbertChart
