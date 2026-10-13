/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTripleComposition
public import FLT.Mazur.EtaleFiniteBranchFiniteDiagram

/-!
# Finite branches for full associative composition diagrams

Three original arrows, their two adjacent composites, and their total
composite lift on one constructed finite etale coefficient cover. The two
parenthesizations retain exactly the same original scheme morphism.
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
local notation "a" => pullback.fst (v ≫ q) p
local notation "b" => pullback.snd (v ≫ q) p

/-- The three arrows, two adjacent composites, and total composite, in that order. -/
def associativeLeg (i : Fin 6) : tripleArrows f hL d V c k ⟶ D :=
  ![a ≫ u, a ≫ v, b, a ≫ m, tripleLastPair f hL d V c k ≫ m,
    tripleLeftPair f hL d V c k ≫ m] i

/-- Both parenthesizations give the same last leg on every relative test scheme. -/
theorem associativeLeg_last {T : Over (Spec (.of R))}
    (h : T ⟶ tripleArrows f hL d V c k) :
    h ≫ associativeLeg f hL d V c k 5 =
      h ≫ tripleRightPair f hL d V c k ≫ m := by
  change h ≫ (tripleLeftPair f hL d V c k ≫ m) = _
  rw [fullComposition_associative]

variable [Etale V.hom] [IsOpenImmersion k.left]

instance associativeLeg_etale (i : Fin 6) : Etale (associativeLeg f hL d V c k i).left := by
  fin_cases i
  · exact inferInstanceAs (Etale ((a).left ≫ (u).left))
  · exact inferInstanceAs (Etale ((a).left ≫ (v).left))
  · exact tripleArrows_third_etale f hL d V c k
  · exact inferInstanceAs (Etale ((a).left ≫ (m).left))
  · exact inferInstanceAs (Etale ((tripleLastPair f hL d V c k).left ≫ (m).left))
  · exact inferInstanceAs (Etale ((tripleLeftPair f hL d V c k).left ≫ (m).left))

variable [IsAffine A.left]

/-- Every original associative diagram has a finite etale cover lifting all six arrows. -/
theorem exists_associative_finite_branches (x : (tripleArrows f hL d V c k).left) :
    ∃ (Z W : Over (Spec (.of R))) (b' : W ⟶ A) (t : Z ⟶ W)
      (h : Z ⟶ tripleArrows f hL d V c k) (z : Z.left),
      IsAffine Z.left ∧ IsAffine W.left ∧ Etale b'.left ∧
      Etale t.left ∧ IsFinite t.left ∧ Surjective t.left ∧ Etale h.left ∧
      h ≫ associativeLeg f hL d V c k 0 ≫ p = t ≫ b' ∧ h.left z = x ∧
      ∀ j : Fin 6, ∃ (i : (D).left) (l : Z ⟶ EtaleFiniteBranchAtlas.source p i),
        Etale l.left ∧ h ≫ associativeLeg f hL d V c k j =
          l ≫ EtaleFiniteBranchAtlas.original p i := by
  simpa only [Finset.mem_univ, forall_const] using
    EtaleFiniteBranchDiagram.exists_finite_lifts p (associativeLeg f hL d V c k 0)
      Finset.univ (associativeLeg f hL d V c k) x

end FLT.Mazur.HilbertChart.AffineRestriction
