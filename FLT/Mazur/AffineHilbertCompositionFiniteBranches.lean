/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEtaleComposition
public import FLT.Mazur.EtaleFiniteBranchFiniteDiagram

/-!
# Constructed finite branches compatible with full relation composition

Every original composable pair has a common affine etale neighborhood where
both inputs and their composite lift to the actual finite branch atlas.
This neighborhood is finite etale surjective over an affine etale coefficient
scheme. Independent translation coordinates remain in the full relation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

/-- The first input, second input, and actual composite of the original diagram. -/
def compositionLeg (i : Fin 3) : pullback q p ⟶ D :=
  ![pullback.fst q p, pullback.snd q p, fullComposition f hL d V c k] i

/-- Leg zero is the complete first relation arrow. -/
theorem compositionLeg_zero : compositionLeg f hL d V c k 0 = pullback.fst q p := rfl

/-- Leg one is the complete second relation arrow. -/
theorem compositionLeg_one : compositionLeg f hL d V c k 1 = pullback.snd q p := rfl

/-- Leg two is their actual original composite. -/
theorem compositionLeg_two :
    compositionLeg f hL d V c k 2 = fullComposition f hL d V c k := rfl

variable [Etale V.hom] [IsOpenImmersion k.left]

instance compositionLeg_etale (i : Fin 3) : Etale (compositionLeg f hL d V c k i).left := by
  fin_cases i
  · exact fullComposition_first_etale f hL d V c k
  · exact fullComposition_second_etale f hL d V c k
  · exact fullComposition_etale f hL d V c k

variable [IsAffine A.left]

/-- A constructed finite etale cover simultaneously carries both inputs and their composite. -/
theorem exists_composition_finite_branches (x : (pullback q p).left) :
    ∃ (Z W : Over (Spec (.of R))) (b : W ⟶ A) (t : Z ⟶ W)
      (a : Z ⟶ pullback q p) (z : Z.left),
      IsAffine Z.left ∧ IsAffine W.left ∧ Etale b.left ∧
      Etale t.left ∧ IsFinite t.left ∧ Surjective t.left ∧ Etale a.left ∧
      a ≫ pullback.fst q p ≫ p = t ≫ b ∧ a.left z = x ∧
      ∀ j : Fin 3, ∃ (i : (D).left) (h : Z ⟶ EtaleFiniteBranchAtlas.source p i),
        Etale h.left ∧ a ≫ compositionLeg f hL d V c k j =
          h ≫ EtaleFiniteBranchAtlas.original p i := by
  simpa only [Finset.mem_univ, forall_const] using
    EtaleFiniteBranchDiagram.exists_finite_lifts p (pullback.fst q p) Finset.univ
      (compositionLeg f hL d V c k) x

end FLT.Mazur.HilbertChart.AffineRestriction
