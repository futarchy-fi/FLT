/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularComparisonCoherence
public import FLT.Mazur.CompatibleSubgroupBaseChangeCoherence

/-!
# Arbitrary base change of constructed singular orbit comparisons

Reconstructing from the pulled full markings gives exactly the pullback of
the original comparison. Direct and iterated pullbacks consequently retain
the same subgroup map and the original full curve comparison.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve
open FiniteSubgroup GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (ψ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ F.group))
  (e : E ≅ F) (he : ∀ i, φ i ≫ e.hom.group = ψ i)
  (H : E.FiniteSubgroup n) (J : F.FiniteSubgroup n)
  (hH : H.ideal = E.cyclicMarkingIdeal φ) (hJ : J.ideal = F.cyclicMarkingIdeal ψ)

include he in
/-- Every pulled cyclic label retains the actual pulled full curve comparison. -/
theorem singularOrbitLabel_baseChange (g : T ⟶ S) (i : Multiplicative (ZMod n)) :
    pullCyclicMarking g φ i ≫ ((baseChangeFunctor g).mapIso e).hom.group =
      pullCyclicMarking g ψ i := by
  change pullSection g (φ i) ≫ (Over.pullback g).map e.hom.group = pullSection g (ψ i)
  rw [← section_comp, he]

include hH in
/-- The exact full orbit ideal remains exact over every new base scheme. -/
theorem singularOrbitIdeal_baseChange (g : T ⟶ S) :
    (H.baseChange g).ideal = (E.baseChange g).cyclicMarkingIdeal (pullCyclicMarking g φ) := by
  rw [baseChange_ideal, hH, cyclicMarkingIdeal_baseChange]

/-- Construct the comparison again using the actual pulled markings and orbit ideals. -/
def singularOrbitComparisonBaseChange (g : T ⟶ S) :
    CompatibleIso (H.baseChange g) (J.baseChange g) :=
  singularOrbitCompatibleIso (E := E.baseChange g) (F := F.baseChange g)
    (pullCyclicMarking g φ) (pullCyclicMarking g ψ) ((baseChangeFunctor g).mapIso e)
    (singularOrbitLabel_baseChange φ ψ e he g) (H.baseChange g) (J.baseChange g)
    (singularOrbitIdeal_baseChange φ H hH g) (singularOrbitIdeal_baseChange ψ J hJ g)

/-- Reconstruction commutes with base change as an equality of full compatible comparisons. -/
theorem singularOrbitComparisonBaseChange_eq (g : T ⟶ S) :
    singularOrbitComparisonBaseChange φ ψ e he H J hH hJ g =
      (singularOrbitCompatibleIso φ ψ e he H J hH hJ).baseChange g := by
  apply CompatibleIso.ext_curve
  change (singularOrbitCompatibleIso _ _ _ _ _ _ _ _).curve =
    (baseChangeFunctor g).mapIso (singularOrbitCompatibleIso φ ψ e he H J hH hJ).curve
  rw [singularOrbitCompatibleIso_curve, singularOrbitCompatibleIso_curve]

/-- Direct reconstruction agrees with iterated reconstruction through the actual comparisons. -/
theorem singularOrbitComparisonBaseChange_comp (g : T ⟶ S) (k : U ⟶ T) :
    (compatibleBaseChangeComp H g k).trans
        ((singularOrbitComparisonBaseChange φ ψ e he H J hH hJ g).baseChange k) =
      (singularOrbitComparisonBaseChange φ ψ e he H J hH hJ (k ≫ g)).trans
        (compatibleBaseChangeComp J g k) := by
  rw [singularOrbitComparisonBaseChange_eq, singularOrbitComparisonBaseChange_eq]
  exact CompatibleIso.baseChange_comp_natural _ g k

end FLT.Mazur.GeneralizedEllipticCurve
