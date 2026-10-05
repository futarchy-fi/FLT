/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupIntegralEvaluation
public import FLT.Mazur.EllipticSubgroupClosureGluing
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Integral sections of the glued subgroup closure

Every actual subgroup point extends to the glued Y/Z closure. The construction
uses a unit coordinate of its primitive lift and the proved kernel factorization.
On the chosen chart it is a closed immersion and a section of the base map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.EllipticSubgroupChart

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)

/-- An actual integral subgroup point of one closure chart. -/
def integralChartPoint (j : Fin 3) (P : H)
    (hj : IsUnit ((primitiveLift A W P.1).coords j)) :
    Spec (.of A) ⟶ closureChart A W H j :=
  Spec.map (CommRingCat.ofHom (integralClosureEvaluation A W H j P hj).toRingHom)

/-- In its integral chart the point section is a closed immersion. -/
instance integralChartPoint_isClosedImmersion (j : Fin 3) (P : H)
    (hj : IsUnit ((primitiveLift A W P.1).coords j)) :
    IsClosedImmersion (integralChartPoint A W H j P hj) :=
  IsClosedImmersion.spec_of_surjective _
    (integralClosureEvaluation_surjective A W H j P hj)

/-- The integral chart point lies over the identity of the valuation-ring base. -/
@[reassoc (attr := simp)] theorem integralChartPoint_toBase (j : Fin 3) (P : H)
    (hj : IsUnit ((primitiveLift A W P.1).coords j)) :
    integralChartPoint A W H j P hj ≫ closureChartToBase A W H j = 𝟙 _ := by
  have he : (integralClosureEvaluation A W H j P hj).toRingHom.comp
      (algebraMap A (Closure A W H j)) = RingHom.id A := by
    apply RingHom.ext
    intro a
    exact integralClosureEvaluation_algebraMap A W H j P hj a
  simpa only [integralChartPoint, closureChartToBase, CommRingCat.ofHom_comp,
    Spec.map_comp, CommRingCat.ofHom_id, Spec.map_id] using
    congrArg (fun f : A →+* A => Spec.map (CommRingCat.ofHom f)) he

/-- The Y/Z unit cover selects an integral extension of every subgroup point. -/
def integralSection (P : H) : Spec (.of A) ⟶ gluedClosure A W H 1 2 := by
  classical
  exact if hj : IsUnit ((primitiveLift A W P.1).coords 1) then
    integralChartPoint A W H 1 P hj ≫ closureLeft A W H 1 2
  else
    integralChartPoint A W H 2 P
      (((primitiveLift A W P.1).unit_Y_or_Z A W).resolve_left hj) ≫ closureRight A W H 1 2

/-- The constructed extension is a section of the actual glued structural map. -/
@[reassoc (attr := simp)] theorem integralSection_toBase (P : H) :
    integralSection A W H P ≫ closureToBase A W H 1 2 = 𝟙 _ := by
  unfold integralSection
  split <;> simp only [Category.assoc, closureLeft_toBase, closureRight_toBase,
    integralChartPoint_toBase]

/-- In particular the structural morphism of the subgroup closure is surjective. -/
instance closureToBase_surjective : Surjective (closureToBase A W H 1 2) := by
  constructor
  intro x
  refine ⟨integralSection A W H 0 x, ?_⟩
  change (integralSection A W H 0 ≫ closureToBase A W H 1 2) x = x
  rw [integralSection_toBase]
  rfl

end FLT.Mazur.EllipticSubgroupChart
