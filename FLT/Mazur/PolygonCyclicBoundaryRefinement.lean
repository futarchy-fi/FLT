/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCyclicBoundaryDivisor
public import FLT.Mazur.PolygonParameterMarkingBaseChange

/-!
# Parameter refinement of the actual invariant boundary divisor

The full cyclic product commutes with arbitrary parameter base change through
the original pullback composition comparison. Its canonical positive-line
comparison preserves the original divisor section, including on field extensions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.PolygonCyclicBoundary
open PolygonPinching PolygonUniversalAction PolygonParameterTranslation FCurve
open CyclicBoundaryParameter
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] translationIso
  PolygonMarkingBaseChange.markingIdeal movedMarkingIdeal
variable (K : Type) [Field K] (m : ℕ) [NeZero m] (hm : 0 < m)
  {C : Over (Spec (.of K))} (p : components K m ⟶ C) (q : nodes K m ⟶ C)
  (h : IsPushout (toComponents K m hm) (toNodes K m) p q)
  (n : ℕ) [NeZero n] {T U : Scheme} (g : T ⟶ Spec (.of K))
  (f : Over.mk g ⟶ parameter (G K m) n) (a : Kˣ) (i : Fin m) (k : U ⟶ T)
local notation "δ" => Over.Hom.left (NatTrans.app (Iso.inv (Over.pullbackComp k g)) C)
local notation "π" => pullback.fst (Over.hom (Functor.obj (Over.pullback g) C)) k

/-- The refined actual cyclic section is the existing composite-pullback parameter. -/
theorem cyclicSection_refine (j : Multiplicative (ZMod n)) :
    parameterBaseChange K m g k (markedSection (G K m) n g f (1, 1, j)) =
      markedSection (G K m) n (k ≫ g) (refine (G K m) n g f k) (1, 1, j) :=
  section_refine (G K m) n g f k (1, 1, j)

/-- Every original translated factor survives the actual composition chart. -/
theorem labelIdeal_refine (j : Multiplicative (ZMod n)) :
    (labelIdeal K m hm p q h n (k ≫ g) (refine (G K m) n g f k) a i j).comap δ =
      (labelIdeal K m hm p q h n g f a i j).comap π := by
  unfold labelIdeal
  rw [← cyclicSection_refine K m n g f k j]
  exact movedMarkingIdeal_baseChange K m hm p q h g k _ a i

/-- The complete cyclic product, including collisions, survives arbitrary parameter refinement. -/
theorem orbitIdeal_refine :
    (orbitIdeal K m hm p q h n (k ≫ g) (refine (G K m) n g f k) a i).comap δ =
      (orbitIdeal K m hm p q h n g f a i).comap π := by
  simp only [orbitIdeal, idealSheaf_comap_prod, labelIdeal_refine]

/-- The actual positive-line comparison on the iterated parameter base change. -/
irreducible_def orbitRefinementLine :
    (Scheme.Modules.pullback δ).obj
      (orbitLine K m hm p q h n (k ≫ g) (refine (G K m) n g f k) a i) ≅
        divisorLineBundle ((orbitIdeal K m hm p q h n g f a i).comap π)
          (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
            (orbitIdeal_cartier K m hm p q h n g f a i)).1 := by
  let hs := (orbitIdeal_cartier K m hm p q h n (k ≫ g)
    (refine (G K m) n g f k) a i).1
  let ht := (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
    (orbitIdeal_cartier K m hm p q h n g f a i)).1
  let he := orbitIdeal_refine K m hm p q h n g f a i k
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  exact divisorLinePullbackIsoOfEq _ hs ht he

/-- Refinement preserves the original cyclic product section without rescaling it. -/
theorem orbitRefinementLine_section :
    DivisorLineSectionCompatible δ
      (orbitIdeal_cartier K m hm p q h n (k ≫ g) (refine (G K m) n g f k) a i).1
      (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
        (orbitIdeal_cartier K m hm p q h n g f a i)).1
      (orbitRefinementLine K m hm p q h n g f a i k) := by
  let hs := (orbitIdeal_cartier K m hm p q h n (k ≫ g)
    (refine (G K m) n g f k) a i).1
  let ht := (relativeCartierBaseChange ((Over.pullback g).obj C).hom k _
    (orbitIdeal_cartier K m hm p q h n g f a i)).1
  let he := orbitIdeal_refine K m hm p q h n g f a i k
  let _ := idealModulePullbackHom_isIso_of_cartier _ hs (he.symm ▸ ht)
  rw [orbitRefinementLine_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

end FLT.Mazur.PolygonCyclicBoundary
