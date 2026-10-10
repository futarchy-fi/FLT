/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicSectionClosed
public import FLT.Mazur.ExactOrderCyclicPowers
public import FLT.Mazur.GeneralizedCurveSubgroupIdeal

/-!
# The finite etale subgroup of a rational exact-order point

A rational section of the smooth group with exact order n embeds the constant
cyclic group as an actual finite etale closed subgroup. Its component labelled
one maps to the original point. No cyclicity or ampleness is assumed here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.GeneralizedEllipticCurve

variable {K : Type} [Field K] (E : GeneralizedEllipticCurve (Spec (.of K)))
  {n : ℕ} [NeZero n] (P : 𝟙_ (Over (Spec (.of K))) ⟶ E.group) (ho : orderOf P = n)

/-- The exact-order point's cyclic subgroup with its actual closed group inclusion. -/
def rationalCyclicSubgroup : E.FiniteSubgroup n := by
  have : IsProper E.curve.hom := E.family.family.1
  have : IsSeparated E.group.hom := by
    rw [← E.inclusion.w]
    infer_instance
  exact
    { carrier := ConstantCyclicGroup.model (Spec (.of K)) n
      inclusion := ConstantCyclicSectionMap.toScheme (ExactOrderCyclicPowers.powersHom P ho)
      closed := ConstantCyclicSectionClosed.closed _
        (ExactOrderCyclicPowers.powersHom_injective P ho)
      degree := ConstantCyclicFiniteEtale.degree K n }

/-- This actual subgroup is etale over the original rational base field. -/
theorem rationalCyclicSubgroup_etale : Etale (E.rationalCyclicSubgroup P ho).carrier.hom :=
  ConstantCyclicFiniteEtale.etale K n

/-- The component-one section is the specified generator in the subgroup scheme. -/
def rationalCyclicGenerator :
    𝟙_ (Over (Spec (.of K))) ⟶ (E.rationalCyclicSubgroup P ho).carrier :=
  ConstantCyclicGroup.component (Spec (.of K)) n 1

/-- Every subgroup component retains its original multiple of the rational point. -/
theorem rationalCyclicSubgroup_component (k : ℕ) :
    ConstantCyclicGroup.component (Spec (.of K)) n (k : ZMod n) ≫
      (E.rationalCyclicSubgroup P ho).inclusion = P ^ k := by
  change ConstantCyclicGroup.component (Spec (.of K)) n (k : ZMod n) ≫
    ConstantCyclicSectionMap.toScheme (ExactOrderCyclicPowers.powersHom P ho) = _
  rw [ConstantCyclicSectionMap.component_toScheme, ExactOrderCyclicPowers.powersHom_natCast]

/-- The specified subgroup generator maps exactly to the original rational point. -/
theorem rationalCyclicGenerator_inclusion :
    E.rationalCyclicGenerator P ho ≫ (E.rationalCyclicSubgroup P ho).inclusion = P := by
  simpa only [rationalCyclicGenerator, Nat.cast_one, pow_one] using
    E.rationalCyclicSubgroup_component P ho 1

end FLT.Mazur.GeneralizedEllipticCurve
