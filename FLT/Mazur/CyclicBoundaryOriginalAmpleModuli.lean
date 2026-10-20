/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleModuli
public import FLT.Mazur.CyclicBoundaryTestSubgroup

/-!
# The ample modular map retains each original boundary test

The divisor of the subgroup reconstructed from the original test is ample
exactly on the constructed open. The modular transformation returns its full
curve/subgroup class, using the actual base-change comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom] {T : Scheme}
local notation "P" => cyclicFaithfulParameter E.group n
local notation "H" => faithfulUniversalSubgroup E n

/-- Ampleness of the original reconstructed test subgroup is exactly open membership. -/
theorem faithfulTestSubgroup_isAmple_iff_range (u : T ⟶ (P).left) :
    (faithfulTestSubgroup E n u).IsAmple ↔ Set.range u ⊆ ampleParameterOpen E n :=
  (faithfulTestSubgroupPullbackIso E n u).isAmple_iff.trans
    ((H).isAmple_baseChange_iff_range (faithfulUniversalSubgroup_cartier E n).1 u)

/-- The original test subgroup compares with the actual pulled-back universal ample level. -/
def ampleTestOriginalIso (u : T ⟶ ampleParameter E n) :
    CompatibleIso (faithfulTestSubgroup E n (u ≫ (ampleParameterOpen E n).ι))
      ((ampleUniversalLevel E n).val.2.baseChange u) :=
  (faithfulTestSubgroupPullbackIso E n (u ≫ (ampleParameterOpen E n).ι)).trans
    ((H).compatibleBaseChangeComp (ampleParameterOpen E n).ι u)

/-- The full original reconstructed curve and subgroup on every ample parameter test. -/
def ampleTestLevel (u : T ⟶ ampleParameter E n) : ampleCyclicLevels T n :=
  ⟨⟨E.baseChange ((u ≫ (ampleParameterOpen E n).ι) ≫ (P).hom),
      faithfulTestSubgroup E n (u ≫ (ampleParameterOpen E n).ι)⟩,
    (ampleTestOriginalIso E n u).ampleCyclic_iff.mpr
      (ampleCyclicLevelsPullback u n (ampleUniversalLevel E n)).property⟩

/-- The actual modular transformation returns the original test's full level class. -/
theorem ampleModuliMap_apply_original (u : T ⟶ ampleParameter E n) :
    (ampleModuliMap E n).app (Opposite.op T) (ULift.up u) =
      Quotient.mk _ (ampleTestLevel E n u) :=
  Quotient.sound ⟨(ampleTestOriginalIso E n u).symm⟩

/-- The actual original reconstructed test is ample exactly when its unique open lift exists. -/
theorem faithfulTestSubgroup_ample_iff_existsUnique (u : T ⟶ (P).left) :
    (faithfulTestSubgroup E n u).IsAmple ↔
      ∃! v : T ⟶ ampleParameter E n, v ≫ (ampleParameterOpen E n).ι = u :=
  (faithfulTestSubgroupPullbackIso E n u).isAmple_iff.trans (ampleParameter_criterion E n u)

end FLT.Mazur.CyclicBoundaryParameter
