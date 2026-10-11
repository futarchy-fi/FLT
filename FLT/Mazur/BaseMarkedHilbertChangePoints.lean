/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseMarkedHilbertChangePullback

/-!
# Base change on original relative points and Picard classes

The scheme pullback gives a unique point over a prescribed source-base map
with the original Picard class. Both coordinates remain in the universal property.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme} (f : X ⟶ Spec (.of R))
  [Algebra.FiniteType ℤ R] [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {V W : Over (Spec (.of R))} (b : W ⟶ V)
  {ι : Type} (a : ι → BaseMarkedHilbertIndex f V)
local notation "aW" => fun i ↦ baseMarkedIndexChange f b (a i)

/-- The actual base-change square is cartesian among original relative tests as well. -/
theorem baseMarkedGluedChange_over_isPullback :
    IsPullback (baseMarkedGluedChange f hL b a) (baseMarkedGluedBase f hL W aW)
      (baseMarkedGluedBase f hL V a) b :=
  (baseMarkedGluedChange_isPullback f hL b a).of_map (Over.forget _)
    (baseMarkedGluedChange_base f hL b a)

variable {U : Over (Spec (.of R))} (p : U ⟶ baseMarkedGluedTest f hL V a) (k : U ⟶ W)
  (hb : p ≫ baseMarkedGluedBase f hL V a = k ≫ b)

/-- The constructed lift retains the prescribed map to the new translation base. -/
def baseMarkedGluedChangeLift : U ⟶ baseMarkedGluedTest f hL W aW :=
  (baseMarkedGluedChange_over_isPullback f hL b a).lift p k hb

@[reassoc]
theorem baseMarkedGluedChangeLift_comparison :
    baseMarkedGluedChangeLift f hL b a p k hb ≫ baseMarkedGluedChange f hL b a = p :=
  (baseMarkedGluedChange_over_isPullback f hL b a).lift_fst _ _ _

@[reassoc]
theorem baseMarkedGluedChangeLift_base :
    baseMarkedGluedChangeLift f hL b a p k hb ≫ baseMarkedGluedBase f hL W aW = k :=
  (baseMarkedGluedChange_over_isPullback f hL b a).lift_snd _ _ _

/-- The lifted relative point has the unchanged original Picard class. -/
theorem baseMarkedGluedChangeLift_class :
    baseMarkedGluedPoint f hL W aW U (baseMarkedGluedChangeLift f hL b a p k hb) =
      baseMarkedGluedPoint f hL V a U p := by
  rw [← baseMarkedGluedChange_point f hL b a, baseMarkedGluedChangeLift_comparison]

include hb in
/-- The original class and the prescribed new base map characterize the lift uniquely. -/
theorem baseMarkedGluedChange_originalClass_lift :
    ∃! q : U ⟶ baseMarkedGluedTest f hL W aW,
      q ≫ baseMarkedGluedBase f hL W aW = k ∧
        baseMarkedGluedPoint f hL W aW U q = baseMarkedGluedPoint f hL V a U p := by
  refine ⟨baseMarkedGluedChangeLift f hL b a p k hb,
    ⟨baseMarkedGluedChangeLift_base f hL b a p k hb,
      baseMarkedGluedChangeLift_class f hL b a p k hb⟩, ?_⟩
  intro q hq
  apply baseMarkedGluedPoint_injective_over f hL W aW
  · exact hq.1.trans (baseMarkedGluedChangeLift_base f hL b a p k hb).symm
  · exact hq.2.trans (baseMarkedGluedChangeLift_class f hL b a p k hb).symm

end FLT.Mazur.HilbertChart
