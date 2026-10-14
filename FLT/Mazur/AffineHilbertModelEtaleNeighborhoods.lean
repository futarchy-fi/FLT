/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteBranchTargetNeighborhood
public import FLT.Mazur.AffineHilbertModelEtale

/-!
# Finite etale neighborhoods retaining the whole original Picard source

Every point already lying in a constructed effective fppf region has finite
etale branch neighborhoods inside prescribed source and target opens. The
complete original source over each coefficient neighborhood is retained too:
its projection is etale surjective and all kernel tests recover original arrows.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))}
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {T : Over (Spec (.of R))} (w : A ⟶ T)
  (hw : (fst f hL d V c k).left ≫ w.left = (snd f hL d V c k).left ≫ w.left)
variable [LocallyOfFinitePresentation w.left]
local notation "F" => ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)
local notation "E" => modelFppfTarget f hL d V c k w hw
local notation "C" => modelFppfSource f hL d V c k w hw
local notation "π" => modelFppfProjection f hL d V c k w hw
local notation "j" => modelFppfToEffective f hL d V c k w hw ≫
  modelEffectiveToSource f hL d V c k w hw
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

/-- Actual finite branches coexist with complete etale surjective original-source pullbacks. -/
theorem modelFppf_exists_finite_etale_neighborhood
    (Ω : (C).left.Opens) (Ψ : (E).left.Opens)
    (x : (C).left) (hx : x ∈ Ω) (hy : (π).left x ∈ Ψ) :
    ∃ (Z W : Over (Spec (.of R))) (b : W ⟶ E) (t : Z ⟶ W) (a : Z ⟶ C) (z : Z.left),
      IsAffine Z.left ∧ IsAffine W.left ∧ Etale b.left ∧ Etale t.left ∧
        IsFinite t.left ∧ Surjective t.left ∧ Etale a.left ∧
        a ≫ π = t ≫ b ∧ a.left z = x ∧
        Set.range a.left ⊆ Ω ∧ Set.range b.left ⊆ Ψ ∧
        Etale (pullback.snd π b).left ∧ Surjective (pullback.snd π b).left ∧
        ∀ (Q : Over (Spec (.of R))) (x y : Q ⟶ pullback π b),
          x ≫ pullback.snd π b = y ≫ pullback.snd π b →
          ∃! r : Q ⟶ D, r ≫ p = x ≫ pullback.fst π b ≫ j ∧
            r ≫ q = y ≫ pullback.fst π b ≫ j := by
  obtain ⟨Z, W, b, t, a, z, hZ, hW, hb, ht, hf, hs, ha, he, hz, hΩ, hΨ⟩ :=
    EtaleFiniteBranchTargetNeighborhood.exists_cover π Ω Ψ x hx hy
  have H := (IsPullback.of_hasPullback π b).map (Over.forget _)
  have hp : Etale (pullback.snd π b).left :=
    MorphismProperty.of_isPullback H (inferInstanceAs (Etale (π).left))
  have hsur : Surjective (pullback.snd π b).left :=
    MorphismProperty.of_isPullback H (inferInstanceAs (Surjective (π).left))
  refine ⟨Z, W, b, t, a, z, hZ, hW, hb, ht, hf, hs, ha, he, hz, hΩ, hΨ, hp, hsur, ?_⟩
  intro Q x y hxy
  have heq : (x ≫ pullback.fst π b) ≫ π = (y ≫ pullback.fst π b) ≫ π := by
    calc
      _ = (x ≫ pullback.snd π b) ≫ b := by simp only [Category.assoc, pullback.condition]
      _ = (y ≫ pullback.snd π b) ≫ b := congrArg (fun a ↦ a ≫ b) hxy
      _ = _ := by simp only [Category.assoc, pullback.condition]
  simpa only [Category.assoc] using
    modelFppf_original_lift f hL d V c k w hw
      (x ≫ pullback.fst π b) (y ≫ pullback.fst π b) heq

end FLT.Mazur.HilbertChart.AffineRestriction
