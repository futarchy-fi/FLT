/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingSingularCriterion

/-!
# The original cyclic labels generate the constructed singular divisor subgroup

Every label lifts through the actual closed subgroup. The lifted generator has
order dividing n and its full Cartier orbit is precisely the subgroup ideal,
so the multiplication construction is cyclic even when labels coincide.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  [SmoothOfRelativeDimension 1 E.group.hom]
  (hm : ClosedGroupIdeal.multiplicationEquation E.group (E.cyclicMarkingGroupIdeal φ) = 0)
local notation "H" => E.singularCyclicDivisorSubgroup φ hm

/-- Each original label lifts through the full constructed subgroup, with its nilpotents. -/
def singularCyclicDivisorLabel (i : ZMod n) : 𝟙_ (Over S) ⟶ (H).carrier :=
  ClosedGroupIdeal.lift E.group (E.cyclicMarkingGroupIdeal φ) (φ (.ofAdd i))
    ((FCurve.idealModulePullbackι_eq_zero_iff _ _).mpr
      (E.cyclicMarkingGroupIdeal_le_section φ i))

/-- The lifted label is exactly the given section in the original smooth group. -/
@[reassoc] theorem singularCyclicDivisorLabel_inclusion (i : ZMod n) :
    E.singularCyclicDivisorLabel φ hm i ≫ (H).inclusion = φ (.ofAdd i) :=
  ClosedGroupIdeal.lift_inclusion _ _ _ _

/-- The residue-one section is the constructed subgroup's original cyclic generator. -/
def singularCyclicDivisorGenerator : 𝟙_ (Over S) ⟶ (H).carrier :=
  E.singularCyclicDivisorLabel φ hm 1

/-- Every generator power retains its original cyclic label in the smooth group. -/
theorem singularCyclicDivisorGenerator_pow_inclusion (r : ℕ) :
    (E.singularCyclicDivisorGenerator φ hm ^ r) ≫ (H).inclusion =
      φ (.ofAdd (r : ZMod n)) := by
  rw [MonObj.pow_comp, singularCyclicDivisorGenerator,
    singularCyclicDivisorLabel_inclusion]
  simp only [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, _root_.mul_one]

/-- The original generator has order dividing n as a section of the entire subgroup. -/
theorem singularCyclicDivisorGenerator_torsion :
    E.singularCyclicDivisorGenerator φ hm ^ n = 1 := by
  have : Mono (H).inclusion := Over.mono_of_mono_left _
  apply (cancel_mono (H).inclusion).mp
  rw [singularCyclicDivisorGenerator_pow_inclusion, ZMod.natCast_self, MonObj.one_comp]
  exact map_one φ

/-- The constructed generator is Cartier on the entire possibly singular curve. -/
theorem singularCyclicDivisorGenerator_cartier :
    (H).IsCartierGenerator (E.singularCyclicDivisorGenerator φ hm) := by
  refine ⟨E.singularCyclicDivisorGenerator_torsion φ hm, ?_, ?_⟩
  · rw [singularCyclicDivisorSubgroup_ideal]
    exact E.cyclicMarkingIdeal_smoothOpen_cartier φ
  · rw [singularCyclicDivisorSubgroup_ideal, cyclicMarkingIdeal]
    apply Finset.prod_congr rfl
    intro i _
    have he : (E.singularCyclicDivisorGenerator φ hm ^ i.val) ≫ (H).curveMap =
        φ (.ofAdd (i.val : ZMod n)) ≫ E.inclusion := by
      rw [FiniteSubgroup.curveMap, ← Category.assoc,
        singularCyclicDivisorGenerator_pow_inclusion]
    exact congrArg (fun f ↦ f.left.ker) he.symm

/-- Multiplication closure gives cyclicity without faithful or etale marking hypotheses. -/
theorem singularCyclicDivisorSubgroup_isCyclic : (H).IsCyclic :=
  (E.singularCyclicDivisorGenerator_cartier φ hm).isCyclic H

end FLT.Mazur.GeneralizedEllipticCurve
