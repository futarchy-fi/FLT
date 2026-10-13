/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertRelationNeighborhoods

/-!
# Etale geometry of the full original composition diagram

Both input projections and actual composition are etale. Composition is
proved etale from its first endpoint square, with no quotient hypothesis.
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

/-- The actual original composition, with its canonical pullback source exposed. -/
def fullComposition : pullback q p ⟶ D := (equivalence f hL d V c k).t

/-- Composition retains the first input's first endpoint. -/
@[reassoc]
theorem fullComposition_fst :
    fullComposition f hL d V c k ≫ p = pullback.fst q p ≫ p :=
  (equivalence f hL d V c k).transitivity₁

/-- Composition retains the second input's second endpoint. -/
@[reassoc]
theorem fullComposition_snd :
    fullComposition f hL d V c k ≫ q = pullback.snd q p ≫ q :=
  (equivalence f hL d V c k).transitivity₂

variable [Etale V.hom] [IsOpenImmersion k.left]

instance fullComposition_first_etale : Etale (pullback.fst q p).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback q p).map (Over.forget _)).flip
    (inferInstanceAs (Etale (p).left))

instance fullComposition_second_etale : Etale (pullback.snd q p).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback q p).map (Over.forget _))
    (inferInstanceAs (Etale (q).left))

instance fullComposition_etale : Etale (fullComposition f hL d V c k).left := by
  let _ : Etale ((fullComposition f hL d V c k).left ≫ (p).left) := by
    rw [← Over.comp_left, fullComposition_fst, Over.comp_left]
    infer_instance
  exact Etale.of_comp _ (p).left

end FLT.Mazur.HilbertChart.AffineRestriction
