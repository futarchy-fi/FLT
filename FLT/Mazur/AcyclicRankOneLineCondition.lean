/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointNormalizedAcyclicTests
public import FLT.Mazur.ProperGlobalRankOnePointedDivisor
public import FLT.Mazur.PointNormalizedDivisorUniqueness

/-!
# The intrinsic acyclic rank-one line condition and its full divisors

The condition concerns actual fiber cohomology and actual direct image.
Isomorphism and point normalization preserve it. The canonical existence
construction supplies a full relative Cartier divisor for every such line
on a proper flat geometrically integral family over a locally Noetherian base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.CartierAbel
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} (f : X ⟶ S)

/-- The intrinsic cohomology and direct-image conditions on an actual line sheaf. -/
def AcyclicRankOne (L : X.Modules) : Prop :=
  (∀ s : S, ∀ n, Subsingleton (ModuleH ((pullback (f.fiberι s)).obj L) (n + 1))) ∧
    LocallyFreeRankOne ((pushforward f).obj L)

/-- An actual sheaf isomorphism preserves and detects both conditions. -/
theorem acyclicRankOne_iso {L M : X.Modules} (a : L ≅ M) :
    AcyclicRankOne f L ↔ AcyclicRankOne f M := by
  refine and_congr (forall_congr' fun s ↦ forall_congr' fun n ↦ ?_) ?_
  · exact Equiv.subsingleton_congr
      (moduleHIsoOfIso ((pullback (f.fiberι s)).mapIso a) (n + 1)).toEquiv
  · exact ⟨fun h ↦ h.of_iso ((pushforward f).mapIso a),
      fun h ↦ h.of_iso ((pushforward f).mapIso a.symm)⟩

/-- Actual point normalization preserves and detects the intrinsic condition. -/
theorem acyclicRankOne_normalize (e : S ⟶ X) (L : X.Modules) (hL : LocallyFreeRankOne L) :
    AcyclicRankOne f (SchemePicard.pointNormalizedLine f e L) ↔ AcyclicRankOne f L :=
  SchemePicard.pointNormalizedLine_acyclic_rankOne_iff f e L hL

/-- Equality of pointed classes transfers the intrinsic condition to the actual divisor line. -/
theorem acyclicRankOne_divisor_of_pointedFiber (e : S ⟶ X) (he : e ≫ f = 𝟙 S)
    (L : X.Modules) (hL : LocallyFreeRankOne L) (hA : AcyclicRankOne f L)
    (D : PointedRelativeFiber f e he L hL) :
    AcyclicRankOne f (divisorLineBundle D.val.val D.val.property) := by
  obtain ⟨a⟩ := pointedRelativeFiber_lineIso f e he L hL D
  apply (acyclicRankOne_normalize f e _
    D.val.property.divisorLineBundle_locallyFreeRankOne).mp
  exact (acyclicRankOne_iso f a).mpr ((acyclicRankOne_normalize f e L hL).mpr hA)

/-- Every actual acyclic rank-one line has a full relative Cartier divisor in its Abel fiber. -/
theorem acyclicRankOne_relativeFiber_nonempty [IsLocallyNoetherian S]
    [IsProper f] [Flat f] [GeometricallyIntegral f]
    (L : X.Modules) (hL : LocallyFreeRankOne L) (hA : AcyclicRankOne f L) :
    Nonempty (RelativeFiber f L hL) := by
  have H : IsPullback (𝟙 X) f f (𝟙 S) := IsPullback.of_horiz_isIso ⟨by simp⟩
  let a := (pullbackId X).app L
  have hA' := (acyclicRankOne_iso f a).mpr hA
  exact ⟨relativeFiberCoefficientEquiv f (hL.pullback (𝟙 X)) hL a
    (acyclicRankOneFamilyDivisor H L hL hA'.1 hA'.2)⟩

end FLT.Mazur.CartierAbel
