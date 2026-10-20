/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleAction

/-!
# The ample boundary modular transformation is invariant under relabeling

The invariant class is proved from a compatible isomorphism of the original
full curve and subgroup, and the equality holds on every scheme test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [IsSeparated E.group.hom] [SmoothOfRelativeDimension 1 E.group.hom]
local notation "H" => faithfulUniversalSubgroup E n
local notation "ι" => Scheme.Opens.ι (ampleParameterOpen E n)

/-- The ample universal level retains its whole curve and subgroup under the finite action. -/
def ampleRelabelSubgroupIso (e : RelabelGroup n) :
    CompatibleIso ((ampleUniversalLevel E n).val.2.baseChange (ampleRelabel E n e))
      (ampleUniversalLevel E n).val.2 := by
  have h := faithfulRelabeledTestIso E n (ι) e
  rw [← ampleRelabel_inclusion E n e] at h
  exact ((H).compatibleBaseChangeComp (ι) (ampleRelabel E n e)).symm.trans h

/-- Relabeling fixes the actual universal ample cyclic class. -/
theorem ampleUniversalClass_relabel (e : RelabelGroup n) :
    ampleCyclicClassesPullback (ampleRelabel E n e) n (ampleUniversalClass E n) =
      ampleUniversalClass E n :=
  Quotient.sound ⟨ampleRelabelSubgroupIso E n e⟩

/-- The full original modular class is invariant on every test, including nonreduced tests. -/
theorem ampleModuliMap_relabel {T : Scheme} (u : T ⟶ ampleParameter E n)
    (e : RelabelGroup n) :
    (ampleModuliMap E n).app (Opposite.op T) (ULift.up (u ≫ (ampleAction E n e).hom)) =
      (ampleModuliMap E n).app (Opposite.op T) (ULift.up u) := by
  change ampleCyclicClassesPullback (u ≫ ampleRelabel E n e) n (ampleUniversalClass E n) = _
  rw [ampleCyclicClassesPullback_comp]
  change ampleCyclicClassesPullback u n
    (ampleCyclicClassesPullback (ampleRelabel E n e) n (ampleUniversalClass E n)) = _
  rw [ampleUniversalClass_relabel]
  rfl

end FLT.Mazur.CyclicBoundaryParameter
