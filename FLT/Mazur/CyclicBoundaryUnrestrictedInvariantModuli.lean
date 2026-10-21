/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryUnrestrictedAmpleAction

/-!
# Relabeling fixes the actual unrestricted ample modular transformation

The constructed full curve and subgroup comparison proves invariance on
every scheme test, retaining non-faithful cyclic levels and nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve.FiniteSubgroup CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) (n : ℕ) [NeZero n]
  [SmoothOfRelativeDimension 1 E.group.hom]
local notation "H" => unrestrictedLocusSubgroup E n
local notation "ι" => Scheme.Opens.ι (unrestrictedAmpleOpen E n)

/-- The unrestricted ample universal subgroup is preserved with its whole curve. -/
def unrestrictedAmpleRelabelSubgroupIso (e : RelabelGroup n) :
    CompatibleIso ((unrestrictedAmpleLevel E n).val.2.baseChange
      (unrestrictedAmpleRelabel E n e)) (unrestrictedAmpleLevel E n).val.2 := by
  have h := (unrestrictedRelabeledTestIso E n (ι) e).symm
  rw [← unrestrictedAmpleRelabel_inclusion E n e] at h
  exact ((H).compatibleBaseChangeComp (ι) (unrestrictedAmpleRelabel E n e)).symm.trans h

/-- The original ample cyclic class is fixed by the full finite relabeling group. -/
theorem unrestrictedAmpleClass_relabel (e : RelabelGroup n) :
    ampleCyclicClassesPullback (unrestrictedAmpleRelabel E n e) n
      (unrestrictedAmpleClass E n) = unrestrictedAmpleClass E n :=
  Quotient.sound ⟨unrestrictedAmpleRelabelSubgroupIso E n e⟩

/-- The full modular transformation is invariant on arbitrary scheme tests. -/
theorem unrestrictedAmpleModuliMap_relabel {T : Scheme}
    (u : T ⟶ (unrestrictedAmpleOpen E n).toScheme) (e : RelabelGroup n) :
    (unrestrictedAmpleModuliMap E n).app (Opposite.op T)
        (ULift.up (u ≫ (unrestrictedAmpleAction E n e).hom)) =
      (unrestrictedAmpleModuliMap E n).app (Opposite.op T) (ULift.up u) := by
  change ampleCyclicClassesPullback (u ≫ unrestrictedAmpleRelabel E n e) n
    (unrestrictedAmpleClass E n) = _
  rw [ampleCyclicClassesPullback_comp]
  change ampleCyclicClassesPullback u n
    (ampleCyclicClassesPullback (unrestrictedAmpleRelabel E n e) n
      (unrestrictedAmpleClass E n)) = _
  rw [unrestrictedAmpleClass_relabel]
  rfl

end FLT.Mazur.CyclicBoundaryParameter
