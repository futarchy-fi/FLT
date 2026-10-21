/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonAmpleBaseChange
public import FLT.Mazur.CyclicBoundaryAmpleInvariantModuli
public import FLT.Mazur.CompatibleSubgroupBaseChangeCompEq

/-!
# The arithmetic faithful chart retains its original universal level

The passage through the ample open represents the actual faithful universal
curve and subgroup. The original finite relabeling action preserves this map
on every scheme test, rather than only on geometric isomorphism classes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open CyclicBoundaryParameter GeneralizedEllipticCurve.FiniteSubgroup CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] (t : R) (ht : IsUnit (1 + 432 * t))
  (n : ℕ) [NeZero n]
local notation "E" => curve t ht
local notation "B" => cyclicFaithfulParameter (GeneralizedEllipticCurve.group (E)) n
local notation "H" => faithfulUniversalSubgroup (E) n
local notation "I" => ampleParameterOpen (E) n
local notation "j" => faithfulToAmple t ht n

/-- The original faithful universal curve and subgroup form an ample cyclic level. -/
def faithfulAmpleLevel : ampleCyclicLevels (B).left n :=
  ⟨⟨faithfulUniversalCurve (E) n, (H)⟩, faithfulUniversalSubgroup_isCyclic (E) n,
    faithfulUniversalSubgroup_isAmple t ht n⟩

/-- Restricting to the ample chart and back recovers the original full subgroup. -/
def faithfulAmpleSubgroupIso :
    CompatibleIso ((ampleUniversalLevel (E) n).val.2.baseChange (j)) (H) :=
  (compatibleBaseChangeCompEq (H) (I).ι (j) (𝟙 (B).left)
    (faithfulToAmple_inclusion t ht n).symm).symm.trans (compatibleBaseChangeId (H))

/-- The ample chart gives exactly the original faithful arithmetic level class. -/
theorem faithfulAmpleClass :
    ampleCyclicClassesPullback (j) n (ampleUniversalClass (E) n) =
      Quotient.mk _ (faithfulAmpleLevel t ht n) :=
  Quotient.sound ⟨faithfulAmpleSubgroupIso t ht n⟩

/-- On every scheme test the modular transformation is the original universal level pullback. -/
theorem faithfulBoundaryModuliMap_apply {T : Scheme} (u : T ⟶ (B).left) :
    (faithfulBoundaryModuliMap t ht n).app (Opposite.op T) (ULift.up u) =
      ampleCyclicClassesPullback u n (Quotient.mk _ (faithfulAmpleLevel t ht n)) := by
  change ampleCyclicClassesPullback (u ≫ (j)) n (ampleUniversalClass (E) n) = _
  rw [ampleCyclicClassesPullback_comp]
  change ampleCyclicClassesPullback u n
    (ampleCyclicClassesPullback (j) n (ampleUniversalClass (E) n)) = _
  rw [faithfulAmpleClass]

/-- The identification with the ample chart is equivariant for the original finite action. -/
@[reassoc] theorem faithfulToAmple_relabel (e : RelabelGroup n) :
    (faithfulRelabel (E).group n e).left ≫ (j) = (j) ≫ ampleRelabel (E) n e := by
  apply (cancel_mono (I).ι).mp
  rw [Category.assoc, faithfulToAmple_inclusion, Category.comp_id, Category.assoc,
    ampleRelabel_inclusion, faithfulToAmple_inclusion_assoc]

/-- The arithmetic faithful modular transformation is invariant on all scheme-valued tests. -/
theorem faithfulBoundaryModuliMap_relabel {T : Scheme} (u : T ⟶ (B).left)
    (e : RelabelGroup n) :
    (faithfulBoundaryModuliMap t ht n).app (Opposite.op T)
        (ULift.up (u ≫ (faithfulRelabel (E).group n e).left)) =
      (faithfulBoundaryModuliMap t ht n).app (Opposite.op T) (ULift.up u) := by
  change (ampleModuliMap (E) n).app (Opposite.op T)
      (ULift.up ((u ≫ (faithfulRelabel (E).group n e).left) ≫ (j))) =
    (ampleModuliMap (E) n).app (Opposite.op T) (ULift.up (u ≫ (j)))
  rw [Category.assoc, faithfulToAmple_relabel, ← Category.assoc]
  exact ampleModuliMap_relabel (E) n (u ≫ (j)) e

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
