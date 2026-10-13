/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEtaleComposition

/-!
# Actual triple composition and associativity of the full Hilbert relation

The original iterated pullback retains three independent arrows. Both
parenthesizations are actual relative scheme maps and agree by their endpoints.
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
local notation "u" => pullback.fst q p
local notation "v" => pullback.snd q p
local notation "m" => fullComposition f hL d V c k

/-- The actual scheme of three composable original arrows. -/
abbrev tripleArrows : Over (Spec (.of R)) := pullback (v ≫ q) p

local notation "a" => pullback.fst (v ≫ q) p
local notation "b" => pullback.snd (v ≫ q) p

/-- The last two original arrows, as a map to the original composition pullback. -/
def tripleLastPair : tripleArrows f hL d V c k ⟶ pullback q p :=
  pullback.lift (a ≫ v) b (by rw [Category.assoc, pullback.condition])

local notation "l" => tripleLastPair f hL d V c k

/-- First compose the first two arrows, retaining the third original arrow. -/
def tripleLeftPair : tripleArrows f hL d V c k ⟶ pullback q p :=
  pullback.lift (a ≫ m) b (by
    rw [Category.assoc, fullComposition_snd, pullback.condition])

/-- First compose the last two arrows, retaining the first original arrow. -/
def tripleRightPair : tripleArrows f hL d V c k ⟶ pullback q p :=
  pullback.lift (a ≫ u) (l ≫ m) (by
    rw [Category.assoc, Category.assoc, fullComposition_fst]
    simp only [tripleLastPair, pullback.lift_fst_assoc, Category.assoc,
      pullback.condition])

/-- Both actual parenthesizations agree as relative scheme morphisms. -/
theorem fullComposition_associative :
    tripleLeftPair f hL d V c k ≫ m = tripleRightPair f hL d V c k ≫ m := by
  apply hom_ext f hL d V c k
  · simp only [Category.assoc, fullComposition_fst, tripleLeftPair,
      tripleRightPair, pullback.lift_fst_assoc]
  · simp only [Category.assoc, fullComposition_snd, tripleLeftPair,
      tripleRightPair, tripleLastPair, pullback.lift_snd_assoc]

variable [Etale V.hom] [IsOpenImmersion k.left]

instance tripleArrows_first_etale : Etale (a).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (v ≫ q) p).map (Over.forget _)).flip
    (inferInstanceAs (Etale (p).left))

instance tripleArrows_third_etale : Etale (b).left :=
  MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (v ≫ q) p).map (Over.forget _))
    (inferInstanceAs (Etale ((v).left ≫ (q).left)))

instance tripleLastPair_etale : Etale (l).left := by
  let _ : Etale ((l).left ≫ (v).left) := by
    rw [← Over.comp_left]
    change Etale (pullback.lift (a ≫ v) b _ ≫ v).left
    rw [pullback.lift_snd]
    infer_instance
  exact Etale.of_comp _ (v).left

instance tripleLeftPair_etale : Etale (tripleLeftPair f hL d V c k).left := by
  let _ : Etale ((tripleLeftPair f hL d V c k).left ≫ (v).left) := by
    rw [← Over.comp_left]
    change Etale (pullback.lift (a ≫ m) b _ ≫ v).left
    rw [pullback.lift_snd]
    infer_instance
  exact Etale.of_comp _ (v).left

instance tripleRightPair_etale : Etale (tripleRightPair f hL d V c k).left := by
  let _ : Etale ((tripleRightPair f hL d V c k).left ≫ (u).left) := by
    rw [← Over.comp_left]
    change Etale (pullback.lift (a ≫ u) (l ≫ m) _ ≫ u).left
    rw [pullback.lift_fst, Over.comp_left]
    infer_instance
  exact Etale.of_comp _ (u).left

end FLT.Mazur.HilbertChart.AffineRestriction
