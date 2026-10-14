/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEffectiveTargetOpen
public import FLT.Mazur.MonomorphismRelativeOpenBaseChange

/-!
# Genuine flat refinements of the original Picard effective locus

Refine the entire candidate kernel and the entire original Picard relation
by an arbitrary flat, locally finitely presented target map. The constructed
effective open is exactly the pullback of the original effective open.
This does not prove that either open is nonempty or covers its target.
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
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {B : Over (Spec (.of R))} (u : B ⟶ A) {T : Scheme}
  (i : T ⟶ (finiteKernelModel f hL d V c k).left) [Mono i] (w : B.left ⟶ T)
  (h : IsPullback u.left w (finiteKernelProjection f hL d V c k).left i)
local notation "m" => monicModelRelationKernelMap f hL d V c k u i w h
local notation "q" => pullback.fst w w ≫ w
variable {T' : Scheme} (t : T' ⟶ T)

/-- The full original comparison after an actual quotient-target refinement. -/
abbrev monicModelRefinedComparison :=
  MonomorphismRelativeOpen.refinedComparison m q t

/-- The intrinsic effective open computed from the complete refined relation. -/
def monicModelRefinedEffectiveTargetOpen : T'.Opens :=
  MonomorphismRelativeOpen.targetOpen
    (monicModelRefinedComparison f hL d V c k u i w h t) (pullback.snd q t)

/-- Flat refinement preserves the original effective open, including its nilpotents. -/
theorem monicModelRefinedEffectiveTargetOpen_eq [Flat t] [LocallyOfFinitePresentation t] :
    monicModelRefinedEffectiveTargetOpen f hL d V c k u i w h t =
      t ⁻¹ᵁ monicModelEffectiveTargetOpen f hL d V c k u i w h :=
  @MonomorphismRelativeOpen.refined_targetOpen _ _ _ _ m
    (monicModelRelationKernelMap_mono f hL d V c k u i w h) q t _ _

/-- Genuine fppf refinement detects coverage; it cannot create missing coverage. -/
theorem monicModelRefinedEffectiveTargetOpen_top_iff
    [Flat t] [LocallyOfFinitePresentation t] [Surjective t] :
    monicModelRefinedEffectiveTargetOpen f hL d V c k u i w h t = ⊤ ↔
      monicModelEffectiveTargetOpen f hL d V c k u i w h = ⊤ := by
  rw [monicModelRefinedEffectiveTargetOpen_eq]
  constructor
  · intro he
    apply top_le_iff.mp
    intro x _
    obtain ⟨y, rfl⟩ := t.surjective x
    have hy : y ∈ t ⁻¹ᵁ monicModelEffectiveTargetOpen f hL d V c k u i w h := by
      rw [he]
      trivial
    exact hy
  · intro he
    rw [he]
    rfl

end FLT.Mazur.HilbertChart.AffineRestriction
