/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryParameterSections
public import FLT.Mazur.PolygonParameterProductMarking

/-!
# Relabeling-invariant divisors on the original boundary polygon

An actual test of the boundary homomorphism scheme supplies a cyclic list of
translations of an original marked point. Their full product is relative
Cartier and invariant under the common finite group, with all multiplicities.
The construction applies to one-gons and nonreduced parameter schemes as well.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonParameterTranslation FCurve
open CyclicBoundaryParameter CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso
  PolygonMarkingBaseChange.markingIdeal movedMarkingIdeal
variable (K : Type) [Field K] (m : ℕ) [NeZero m] (hm : 0 < m)
  {C : Over (Spec (.of K))} (p : components K m ⟶ C) (q : nodes K m ⟶ C)
  (h : IsPushout (toComponents K m hm) (toNodes K m) p q)
  (n : ℕ) [NeZero n] {T : Scheme} (g : T ⟶ Spec (.of K))
  (f : Over.mk g ⟶ parameter (G K m) n) (a : Kˣ) (i : Fin m)

/-- The original translated marked ideal for each cyclic label of the actual parameter. -/
def labelIdeal (j : Multiplicative (ZMod n)) :
    ((Over.pullback g).obj C).left.IdealSheafData :=
  movedMarkingIdeal K m hm p q h g (markedSection (G K m) n g f (1, 1, j)) a i

/-- The full cyclic product retains collisions as divisor multiplicities. -/
def orbitIdeal : ((Over.pullback g).obj C).left.IdealSheafData :=
  ∏ j, labelIdeal K m hm p q h n g f a i j

/-- Every factor is relative Cartier on the original entire polygon. -/
theorem labelIdeal_cartier (j : Multiplicative (ZMod n)) :
    RelativeEffectiveCartier ((Over.pullback g).obj C).hom
      (labelIdeal K m hm p q h n g f a i j) :=
  movedMarkingIdeal_cartier K m hm p q h g _ a i

/-- The whole actual orbit divisor is relative Cartier over the original parameter base. -/
theorem orbitIdeal_cartier :
    RelativeEffectiveCartier ((Over.pullback g).obj C).hom
      (orbitIdeal K m hm p q h n g f a i) :=
  relativeEffectiveCartier_prod _ Finset.univ _ fun j _ ↦
    labelIdeal_cartier K m hm p q h n g f a i j

/-- The same finite group permutes the actual translated ideal factors. -/
theorem labelIdeal_action (e : RelabelGroup n) (j : Multiplicative (ZMod n)) :
    labelIdeal K m hm p q h n g (f ≫ (action (G K m) n e).hom) a i j =
      labelIdeal K m hm p q h n g f a i (e.2.2.symm j) := by
  unfold labelIdeal
  rw [section_action_cyclic]

/-- The common relabeling fixes the entire divisor, including every scheme-theoretic factor. -/
theorem orbitIdeal_action (e : RelabelGroup n) :
    orbitIdeal K m hm p q h n g (f ≫ (action (G K m) n e).hom) a i =
      orbitIdeal K m hm p q h n g f a i := by
  simp only [orbitIdeal, labelIdeal_action]
  exact Equiv.prod_comp e.2.2.symm.toEquiv _

/-- The original positive divisor line of the boundary orbit. -/
def orbitLine : ((Over.pullback g).obj C).left.Modules :=
  divisorLineBundle (orbitIdeal K m hm p q h n g f a i)
    (orbitIdeal_cartier K m hm p q h n g f a i).1

/-- Relabeling preserves the actual positive line as a sheaf on the original polygon. -/
theorem orbitLine_action (e : RelabelGroup n) :
    orbitLine K m hm p q h n g (f ≫ (action (G K m) n e).hom) a i =
      orbitLine K m hm p q h n g f a i := by
  unfold orbitLine
  congr 1
  exact orbitIdeal_action K m hm p q h n g f a i e

end FLT.Mazur.PolygonCyclicBoundary
