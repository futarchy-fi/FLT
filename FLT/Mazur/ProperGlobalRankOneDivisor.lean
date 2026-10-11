/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperFamilySectionCartierDescent
public import FLT.Mazur.ProperRankOneNormalizedDivisor

/-!
# Canonical full divisors in varying acyclic rank-one families

The original inverse-biduality section has a full relative Cartier ideal on
arbitrary tests of a proper flat geometrically integral family over a locally
Noetherian base. Acyclicity is required only on the changed fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve LineSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {P X T S : Scheme.{0}} [IsLocallyNoetherian S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [IsProper f] [Flat f] [GeometricallyIntegral f] (h : IsPullback p q f g)
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ t : T, ∀ n, Subsingleton
    (ModuleH ((pullback (q.fiberι t)).obj ((pullback p).obj L)) (n + 1)))
  (hN : LocallyFreeRankOne ((pushforward q).obj ((pullback p).obj L)))

/-- Recover an original relative section by descent from a split actual direct-image map. -/
@[irreducible] def SplitDirectImageSection.toAcyclicFamilyRelative
    (a : SplitDirectImageSection q ((pullback p).obj L)) :
    RelativeSection q ((pullback p).obj L) (hL.pullback p) := by
  let s := (twistedSectionPushforwardEquiv q ((pullback p).obj L) a.baseLine.property).symm
    a.map
  have hs : SplitLineAffineNeighborhood.LocallySplit
      (twistedSectionPushforwardEquiv q ((pullback p).obj L) a.baseLine.property s) := by
    simpa only [s, Equiv.apply_symm_apply] using a.locallySplit
  have hc := ProperFamilySectionCartierDescent.regular_and_relativeCartier
    h L hL a.baseLine.property s hs hV
  exact ⟨⟨a.baseLine, s, hc.1⟩, hc.2.2⟩

/-- The canonical normalized section on the actual original varying test family. -/
@[irreducible] def acyclicRankOneFamilySection :
    RelativeSection q ((pullback p).obj L) (hL.pullback p) :=
  (rankOneSplitSection q ((pullback p).obj L) hN).toAcyclicFamilyRelative h L hL hV

/-- The canonical full divisor exists on every acyclic rank-one test. -/
@[irreducible] def acyclicRankOneFamilyDivisor :
    RelativeFiber q ((pullback p).obj L) (hL.pullback p) :=
  relativeSectionToFiber q ((pullback p).obj L) (hL.pullback p)
    (acyclicRankOneFamilySection h L hL hV hN)

/-- The constructed divisor retains every equation of the original normalized zero section. -/
lemma acyclicRankOneFamilyDivisor_ideal :
    (acyclicRankOneFamilyDivisor h L hL hV hN).val.val.val =
      lineSectionZeroIdeal (twist_rankOne q ((pullback p).obj L) (hL.pullback p)
        (acyclicRankOneFamilySection h L hL hV hN).val.baseLine)
        (acyclicRankOneFamilySection h L hL hV hN).val.section_ := by
  unfold acyclicRankOneFamilyDivisor
  rfl

/-- Rank one makes the constructed full divisor unique in its actual relative Abel fiber. -/
theorem acyclicRankOneFamilyDivisor_unique
    (D : RelativeFiber q ((pullback p).obj L) (hL.pullback p)) :
    D = acyclicRankOneFamilyDivisor h L hL hV hN := by
  let _ : Surjective q := MorphismProperty.of_isPullback h inferInstance
  let _ := rankOne_relativeFiber_subsingleton q ((pullback p).obj L) (hL.pullback p) hN
  exact Subsingleton.elim _ _

/-- The entire relative fiber, with flatness and full ideal, is inhabited and unique. -/
@[instance_reducible] def acyclicRankOneFamilyFiberUnique :
    Unique (RelativeFiber q ((pullback p).obj L) (hL.pullback p)) where
  default := acyclicRankOneFamilyDivisor h L hL hV hN
  uniq := acyclicRankOneFamilyDivisor_unique h L hL hV hN

end FLT.Mazur.CartierAbel
