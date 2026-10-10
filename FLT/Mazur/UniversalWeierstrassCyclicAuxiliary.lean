/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryLevel
public import Mathlib.Algebra.Group.Prod

/-!
# Auxiliary level four together with a cyclic generator

The open marking scheme for (Z/4)^2 x Z/p has both the auxiliary basis and
an actual section of exact order p on every nonempty test scheme. The map
forgetting the cyclic generator lands in the previously constructed level-four
scheme. This is a parameterized smooth family; the modular quotient, arithmetic
base restriction, cyclic subgroup divisor, and boundary are separate work.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.UniversalWeierstrass

open AuxiliaryLevel

/-- A full auxiliary level-four labeling together with one cyclic p-label. -/
abbrev CyclicLabels (p : ℕ) := Labels 4 × Multiplicative (ZMod p)

/-- The distinguished cyclic label retains its generator. -/
def cyclicLabel (p : ℕ) : CyclicLabels p := (1, Multiplicative.ofAdd 1)

/-- Its exact order is p, before any geometric interpretation. -/
theorem cyclicLabel_order (p : ℕ) : orderOf (cyclicLabel p) = p := by
  simp [cyclicLabel, Prod.orderOf, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- The actual smooth-family parameter scheme carrying the two kinds of markings. -/
def cyclicAuxiliaryScheme (p : ℕ) [NeZero p] : Over parameterBase :=
  faithfulScheme universalGroup (CyclicLabels p)

/-- Its open immersion in the represented marking equation scheme. -/
def cyclicAuxiliaryInclusion (p : ℕ) [NeZero p] :
    cyclicAuxiliaryScheme p ⟶ homScheme universalGroup (CyclicLabels p) :=
  faithfulInclusion universalGroup (CyclicLabels p)

/-- The original cyclic generator as an actual group-scheme section on any test scheme. -/
def cyclicSection (p : ℕ) [NeZero p] {U : Over parameterBase}
    (f : U ⟶ cyclicAuxiliaryScheme p) : U ⟶ universalGroup :=
  markingOf universalGroup (CyclicLabels p) (f ≫ cyclicAuxiliaryInclusion p) (cyclicLabel p)

/-- Its exact order is proved using the faithful open, not supplied as a record field. -/
theorem cyclicSection_order (p : ℕ) [NeZero p] {U : Over parameterBase}
    (f : U ⟶ cyclicAuxiliaryScheme p) [Nonempty U.left] : orderOf (cyclicSection p f) = p :=
  (orderOf_injective _ (faithful_marking_injective universalGroup (CyclicLabels p) f)
    (cyclicLabel p)).trans (cyclicLabel_order p)

/-- Restriction of labels to the auxiliary factor, on the actual equation schemes. -/
def forgetCyclicEquations (p : ℕ) [NeZero p] :
    cyclicAuxiliaryScheme p ⟶ homScheme universalGroup (Labels 4) :=
  cyclicAuxiliaryInclusion p ≫ relabel universalGroup (MonoidHom.inl _ _)

/-- Forgetting the cyclic label preserves universal faithfulness of the auxiliary basis. -/
theorem forgetCyclicEquations_faithful (p : ℕ) [NeZero p] :
    UniversallyFaithful universalGroup (Labels 4) (forgetCyclicEquations p) := by
  intro V g hV
  let _ := hV
  have h := faithful_marking_injective universalGroup (CyclicLabels p) g
  intro a b hab
  have he : markingOf universalGroup (CyclicLabels p) (g ≫ cyclicAuxiliaryInclusion p)
      (a, 1) = markingOf universalGroup (CyclicLabels p) (g ≫ cyclicAuxiliaryInclusion p)
        (b, 1) := by
    change (g ≫ forgetCyclicEquations p) ≫ value universalGroup (Labels 4) a =
      (g ≫ forgetCyclicEquations p) ≫ value universalGroup (Labels 4) b at hab
    change (g ≫ cyclicAuxiliaryInclusion p) ≫ value universalGroup (CyclicLabels p) (a, 1) =
      (g ≫ cyclicAuxiliaryInclusion p) ≫ value universalGroup (CyclicLabels p) (b, 1)
    simpa only [forgetCyclicEquations, Category.assoc, relabel_value, MonoidHom.inl_apply]
      using hab
  exact congrArg Prod.fst (h he)

/-- The actual morphism forgetting the cyclic generator and retaining level four. -/
def forgetCyclic (p : ℕ) [NeZero p] : cyclicAuxiliaryScheme p ⟶ levelFour :=
  faithfulLift universalGroup (Labels 4) (forgetCyclicEquations p)
    (forgetCyclicEquations_faithful p)

/-- The forgetful map retains every auxiliary coordinate. -/
@[reassoc] theorem forgetCyclic_inclusion (p : ℕ) [NeZero p] :
    forgetCyclic p ≫ auxiliaryInclusion 4 = forgetCyclicEquations p :=
  faithfulLift_inclusion universalGroup (Labels 4) _ _

/-- Independent relabeling of the auxiliary basis and the cyclic generator. -/
def cyclicLabelAction (p : ℕ) :
    MulAut (Labels 4) × MulAut (Multiplicative (ZMod p)) →* MulAut (CyclicLabels p) where
  toFun e := MulEquiv.prodCongr e.1 e.2
  map_one' := by ext a <;> rfl
  map_mul' e f := by ext a <;> rfl

/-- The relabeling group is finite, as required by the invariant-ring quotient foundation. -/
instance cyclicRelabelGroup_finite (p : ℕ) [NeZero p] :
    Finite (MulAut (Labels 4) × MulAut (Multiplicative (ZMod p))) := by
  have h (B : Type) [Group B] [Finite B] : Finite (MulAut B) :=
    Finite.of_injective (fun e : MulAut B => (e : B → B)) DFunLike.coe_injective
  let _ := h (Labels 4)
  let _ := h (Multiplicative (ZMod p))
  infer_instance

/-- The finite relabeling action on the constructed smooth-family parameter scheme. -/
def cyclicAuxiliaryAction (p : ℕ) [NeZero p] :
    MulAut (Labels 4) × MulAut (Multiplicative (ZMod p)) →*
      Aut (cyclicAuxiliaryScheme p).left :=
  (faithfulAction universalGroup (CyclicLabels p)).comp (cyclicLabelAction p)

/-- The action preserves the original Weierstrass parameter map. -/
@[reassoc] theorem cyclicAuxiliaryAction_base (p : ℕ) [NeZero p]
    (e : MulAut (Labels 4) × MulAut (Multiplicative (ZMod p))) :
    (cyclicAuxiliaryAction p e).hom ≫ (cyclicAuxiliaryScheme p).hom =
      (cyclicAuxiliaryScheme p).hom :=
  faithfulAction_base universalGroup (CyclicLabels p) (cyclicLabelAction p e)

end FLT.Mazur.UniversalWeierstrass
