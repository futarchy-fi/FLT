/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NilpotentSectionRestriction
public import FLT.Mazur.EmbeddedStalkNilpotence

/-!
# Nilpotent invariant functions on all opens and at all embedded quotient germs

No affine quotient neighborhoods are needed: every invariant function killed
by a nilpotent source restriction has the source's explicit power bound.
When the quotient comparison is topologically inducing, this controls the
kernel on every stalk as well. Surjectivity of stalk maps remains separate.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme.{u}} {A U : Over S} {A' U' : Over S'}
  {p q : A ⟶ U} {p' q' : A' ⟶ U'}
  (e : CategoryTheory.EquivalenceRelation p q)
  (e' : CategoryTheory.EquivalenceRelation p' q')
  (g : U'.left ⟶ U.left) (r : A'.left ⟶ A.left)
  (hp : r ≫ p.left = p'.left ≫ g) (hq : r ≫ q.left = q'.left ≫ g)
local notation "m" => invariantMap e e' g r hp hq
variable [QuasiCompact g] (n : ℕ) (hn : g.ker ^ n = ⊥)
include hn

/-- All original source domains retain the same power bound, including nonaffine domains. -/
theorem closedSourceRestriction_pow_eq_zero (O : TopologicalSpace.Opens (Orbit e))
    (a : (sourceSheaf e).obj.obj (op O))
    (ha : closedSourceRestriction e e' g r hp hq O a = 0) : a ^ n = 0 := by
  suffices h : ∀ (V : U'.left.Opens) (hV : V = g ⁻¹ᵁ (pullOpen e O).val),
      g.appLE _ V hV.le a = 0 → a ^ n = 0 from
    h _ (invariantMap_sourceOpen_eq e e' g r hp hq O) ha
  intro V hV hv
  subst V
  rw [Scheme.Hom.appLE_eq_app] at hv
  exact NilpotentSectionRestriction.pow_eq_zero g n hn _ a hv

/-- Every invariant section lost under restriction is nilpotent, on every quotient open. -/
theorem invariantMap_section_pow_eq_zero_on (O : TopologicalSpace.Opens (Orbit e))
    (a : (invariantSheaf e).obj.obj (op O)) (ha : (m).c.app (op O) a = 0) :
    a ^ n = 0 := by
  apply invariantSection_ext e O
  rw [map_pow, map_zero]
  exact closedSourceRestriction_pow_eq_zero e e' g r hp hq n hn O _
    ((invariantMap_section_eq_zero_iff e e' g r hp hq O a).mp ha)

/-- A topologically embedded quotient comparison has a nilpotent kernel at every stalk. -/
theorem invariantMap_stalk_pow_eq_zero (hm : Topology.IsInducing (m).base)
    (x : invariantLocallyRingedSpace e')
    (a : (invariantLocallyRingedSpace e).presheaf.stalk ((m).base x))
    (ha : (m).stalkMap x a = 0) : a ^ n = 0 :=
  EmbeddedStalkNilpotence.pow_eq_zero (m).toShHom.hom hm n
    (invariantMap_section_pow_eq_zero_on e e' g r hp hq n hn) x a ha

end FLT.Mazur.RelativeRelationOrbit
