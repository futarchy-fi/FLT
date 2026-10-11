/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointNormalizedFiberCohomology
public import FLT.Mazur.PointNormalizedLineBaseChange
public import FLT.Mazur.ProperLineGlobalAcyclicOpen

/-!
# Point normalization preserves the full acyclic rank-one test condition

The actual sheaf comparison under a compatible pointed family square
transports both fiber cohomology and the actual direct image. These tests
need no finiteness, reducedness, or Noetherianity condition on the new base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemePicard
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ModuleSheafTensor.tensor
variable {X S : Scheme.{0}} (f : X ⟶ S) (e : S ⟶ X)
  (L : X.Modules) (hL : LocallyFreeRankOne L)

include hL in
/-- Normalization preserves and detects the intrinsic acyclic rank-one direct-image condition. -/
theorem pointNormalizedLine_acyclic_rankOne_iff :
    ((∀ s : S, ∀ n, Subsingleton (ModuleH
      ((Scheme.Modules.pullback (f.fiberι s)).obj (pointNormalizedLine f e L)) (n + 1))) ∧
      LocallyFreeRankOne ((Scheme.Modules.pushforward f).obj (pointNormalizedLine f e L))) ↔
    ((∀ s : S, ∀ n, Subsingleton
      (ModuleH ((Scheme.Modules.pullback (f.fiberι s)).obj L) (n + 1))) ∧
      LocallyFreeRankOne ((Scheme.Modules.pushforward f).obj L)) :=
  and_congr (forall_congr' fun s ↦ forall_congr' fun n ↦
    pointNormalizedLine_fiber_vanishing_iff f e L hL s (n + 1))
      (pointNormalizedLine_directImage_rankOne_iff f e L hL)

include hL in
/-- The actual global positive-cohomology open is unchanged by point normalization. -/
theorem pointNormalizedLine_acyclicOpen [IsLocallyNoetherian S] [IsProper f] [Flat f] :
    LineSectionBaseChange.properLineGlobalAcyclicOpen f (pointNormalizedLine f e L)
      (pointNormalizedLine_rankOne f e L hL) =
        LineSectionBaseChange.properLineGlobalAcyclicOpen f L hL := by
  ext s
  exact forall_congr' fun n ↦ pointNormalizedLine_fiber_vanishing_iff f e L hL s (n + 1)

variable {P T : Scheme.{0}} (q : P ⟶ T) (d : T ⟶ P) (p : P ⟶ X) (g : T ⟶ S)
  (hf : p ≫ f = q ≫ g) (he : d ≫ p = g ≫ e)

include hf he hL in
/-- Pulling the normalized original line preserves every actual test-fiber vanishing condition. -/
theorem pointNormalizedLine_test_fiber_vanishing_iff (t : T) (n : ℕ) :
    Subsingleton (ModuleH ((Scheme.Modules.pullback (q.fiberι t)).obj
      ((Scheme.Modules.pullback p).obj (pointNormalizedLine f e L))) n) ↔
      Subsingleton (ModuleH ((Scheme.Modules.pullback (q.fiberι t)).obj
        ((Scheme.Modules.pullback p).obj L)) n) := by
  let a := pointNormalizedLineBaseChangeIso f e q d p g hf he L hL
  exact (Equiv.subsingleton_congr (moduleHIsoOfIso
    ((Scheme.Modules.pullback (q.fiberι t)).mapIso a) n).toEquiv).trans
      (pointNormalizedLine_fiber_vanishing_iff q d _ (hL.pullback p) t n)

include hf he hL in
/-- The actual direct-image line condition is preserved and detected on arbitrary pointed tests. -/
theorem pointNormalizedLine_test_directImage_rankOne_iff :
    LocallyFreeRankOne ((Scheme.Modules.pushforward q).obj
      ((Scheme.Modules.pullback p).obj (pointNormalizedLine f e L))) ↔
      LocallyFreeRankOne ((Scheme.Modules.pushforward q).obj
        ((Scheme.Modules.pullback p).obj L)) := by
  let a := (Scheme.Modules.pushforward q).mapIso
    (pointNormalizedLineBaseChangeIso f e q d p g hf he L hL)
  exact (show LocallyFreeRankOne _ ↔ LocallyFreeRankOne _ from
    ⟨fun h ↦ h.of_iso a, fun h ↦ h.of_iso a.symm⟩).trans
      (pointNormalizedLine_directImage_rankOne_iff q d _ (hL.pullback p))

end FLT.Mazur.SchemePicard
