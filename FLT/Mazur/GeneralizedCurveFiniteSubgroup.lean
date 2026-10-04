/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeCoherence
public import FLT.Mazur.ConstantDegree
public import FLT.Mazur.OverPullbackLocalPushout

/-!
# Finite locally free subgroups of generalized elliptic curves

A subgroup is a closed group subscheme of the actual smooth group, finite
locally free of the specified rank over the base. No cyclicity or ampleness
is part of this definition. Arbitrary base change preserves these data.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve
variable {S T : Scheme} {n : ℕ}

/-- A finite locally free subgroup of rank `n` in the smooth group. -/
structure FiniteSubgroup (E : GeneralizedEllipticCurve S) (n : ℕ) where
  /-- The relative subgroup scheme. -/
  carrier : Over S
  /-- The subgroup is commutative. -/
  [commGroup : CommGrpObj carrier]
  /-- Its inclusion into the actual smooth group. -/
  inclusion : carrier ⟶ E.group
  /-- The inclusion preserves the group law. -/
  [isMonHom : IsMonHom inclusion]
  /-- The subgroup is closed in the smooth group. -/
  [closed : IsClosedImmersion inclusion.left]
  /-- Its structure morphism is finite locally free of the specified rank. -/
  degree : FCurve.FiniteLocallyFreeDegree carrier.hom n

attribute [instance] FiniteSubgroup.commGroup FiniteSubgroup.isMonHom FiniteSubgroup.closed

namespace FiniteSubgroup
variable {E : GeneralizedEllipticCurve S} (H : E.FiniteSubgroup n)

instance : IsFinite H.carrier.hom := H.degree.1
instance : Flat H.carrier.hom := H.degree.2.1
instance : LocallyOfFinitePresentation H.carrier.hom := H.degree.2.2.1

/-- The subgroup map into the whole generalized curve. -/
def curveMap : H.carrier ⟶ E.curve := H.inclusion ≫ E.inclusion

/-- The scheme-theoretic rank is the specified integer at every base point. -/
theorem finrank (s : S) : H.carrier.hom.finrank s = n := H.degree.2.2.2 s

/-- A positive-rank subgroup covers the base. -/
theorem surjective (hn : 0 < n) : Surjective H.carrier.hom := H.degree.surjective hn

/-- Pullback of a finite subgroup along an arbitrary scheme morphism. -/
def baseChange (g : T ⟶ S) : (E.baseChange g).FiniteSubgroup n where
  carrier := (Over.pullback g).obj H.carrier
  inclusion := (Over.pullback g).map H.inclusion
  closed := MorphismProperty.of_isPullback
    (OverPullbackLocalPushout.map_isPullback g H.inclusion).flip H.closed
  degree := H.degree.baseChange g

/-- The map into the curve is the actual pullback of the original subgroup map. -/
@[simp]
theorem baseChange_curveMap (g : T ⟶ S) :
    (H.baseChange g).curveMap = (Over.pullback g).map H.curveMap := by
  simp only [curveMap, baseChange, baseChange_inclusion, pullbackInclusion, Functor.map_comp]

/-- Transport the subgroup along an isomorphism of full DR objects. -/
def transport {F : GeneralizedEllipticCurve S} (e : E ≅ F) : F.FiniteSubgroup n where
  carrier := H.carrier
  inclusion := H.inclusion ≫ e.hom.group
  closed := by
    have : IsIso e.hom.group := inferInstanceAs (IsIso (forgetGroup.map e.hom))
    have : IsIso e.hom.group.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom.group))
    change IsClosedImmersion (H.inclusion.left ≫ e.hom.group.left)
    infer_instance
  degree := H.degree

/-- Transport of the subgroup agrees with transport of its whole-curve map. -/
@[simp]
theorem transport_curveMap {F : GeneralizedEllipticCurve S} (e : E ≅ F) :
    (H.transport e).curveMap = H.curveMap ≫ e.hom.curve := by
  change (H.inclusion ≫ e.hom.group) ≫ F.inclusion = (H.inclusion ≫ E.inclusion) ≫ e.hom.curve
  rw [Category.assoc, ← e.hom.inclusion, Category.assoc]

end FiniteSubgroup
end FLT.Mazur.GeneralizedEllipticCurve
