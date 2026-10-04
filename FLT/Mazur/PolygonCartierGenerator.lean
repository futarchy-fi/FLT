/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFiniteSubgroup
public import FLT.Mazur.GeneralizedCurveCyclicSubgroup
public import FLT.Mazur.PolygonCyclicDivisorOrbit

/-!
# A Cartier generator on the full DR polygon

The all-one divisor's constant cyclic generator satisfies the general
Cartier-generator definition, in every characteristic and for every positive n.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonCartierGenerator
open PolygonPinching PolygonFiniteSubgroup PolygonCyclicDivisor
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C)
  (hn : 0 < n) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The actual section generating the polygon's finite subgroup. -/
def generator : 𝟙_ (Over (Spec (.of K))) ⟶ (subgroup K n p hn q h).carrier :=
  ConstantCyclicGroup.component (Spec (.of K)) n 1 ≫ (overIso K n p hn q h).hom

/-- The generator orbit is the previously computed scheme-theoretic orbit. -/
theorem orbit (i : Fin n) :
    ((generator K n p hn q h ^ i.val) ≫ (subgroup K n p hn q h).curveMap).left =
      PolygonCyclicDivisorOrbit.orbitSection K n p hn q h i := by
  let := commGrpObj K n p hn q h
  have : IsMonHom (overIso K n p hn q h).hom := by
    infer_instance
  rw [generator, ← MonObj.pow_comp, Over.comp_left, PolygonFiniteSubgroup.curveMap]
  rfl

/-- The generator is a Cartier generator of the actual rank-n subgroup. -/
theorem isCartierGenerator :
    (subgroup K n p hn q h).IsCartierGenerator (generator K n p hn q h) := by
  let := commGrpObj K n p hn q h
  have : IsMonHom (overIso K n p hn q h).hom := by infer_instance
  refine ⟨?_, relativeCartier K n p hn q h, ?_⟩
  · rw [generator, ← MonObj.pow_comp, ← ConstantCyclicGenerator.component_natCast,
      ZMod.natCast_self, ConstantCyclicGenerator.component_zero, MonObj.one_comp]
  · simp only [subgroup_ideal, orbit]
    exact PolygonCyclicDivisorOrbit.cyclic_divisor K n p hn q h

/-- The standard polygon carries an fppf-cyclic rank-n subgroup. -/
theorem isCyclic : (subgroup K n p hn q h).IsCyclic :=
  (isCartierGenerator K n p hn q h).isCyclic _

end FLT.Mazur.PolygonCartierGenerator
