/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPositiveEqualityPolygonIso
public import FLT.Mazur.PolygonActionAssociativity
import all FLT.Mazur.WeierstrassDividedPositiveEqualityPushout

/-!
# The split group acts on the actual positive-start equality fiber

Scaling and cyclic rotation descend through the proved original cocone.
Both the component and node formulas retain the original cyclic indexing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open MonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s + 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s + 1) ≤ depth)
  (hp : 2 * (start + s + 1) = depth)
local notation "K" => ResidueField R
local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)
local notation "Z" => positiveEqualityCycleComponent hπ data D s hs hstart hk hp
local notation "N" => positiveEqualityCycleNormalization hπ data D s hs hstart hk hp
local notation "Q" => positiveEqualityCycleNodes hπ data D s hs hstart hk
local notation "C" => Over.mk p
local notation "G" => PolygonSplitGroup.model K (2 * s + 4)
local notation "H" => positiveEqualityCycleCocone_isPushout hπ data D s hs hstart hk hp

/-- The whole original residue fiber receives the split group's scaling and rotation action. -/
def positiveEqualityCycleAction : G ⊗ C ⟶ C :=
  PolygonUniversalAction.act K (2 * s + 4) (by omega) N Q H

local notation "A" => positiveEqualityCycleAction hπ data D s hs hstart hk hp

/-- On each complete original component, the action scales and rotates its original index. -/
@[reassoc] theorem positiveEqualityCycleAction_component
    (a : ZMod (2 * s + 4)) (i : Fin (2 * s + 4)) :
    (PolygonSplitGroup.component K (2 * s + 4) a ⊗ₘ Z i) ≫ A =
      ProjectiveLineUniversalAction.act K ≫ Z (PolygonPinching.rotateIndex a i) := by
  simpa only [positiveEqualityCycleAction, positiveEqualityCycleNormalization_ι] using
    PolygonUniversalAction.component_act K (2 * s + 4) (by omega) N Q H a i

/-- The action keeps the actual node sections and rotates them in the proved cyclic order. -/
@[reassoc] theorem positiveEqualityCycleAction_node
    (a : ZMod (2 * s + 4)) (i : Fin (2 * s + 4)) :
    (PolygonSplitGroup.component K (2 * s + 4) a ⊗ₘ
        equalityNodeOverSection hπ data D s hs hk
          (positiveEqualityCycleNodeIndex start s hstart i)) ≫ A =
      CartesianMonoidalCategory.snd (MultiplicativeGroupScheme.gm K) (PolygonPinching.point K) ≫
        equalityNodeOverSection hπ data D s hs hk
          (positiveEqualityCycleNodeIndex start s hstart (PolygonPinching.rotateIndex a i)) := by
  simpa only [positiveEqualityCycleAction, positiveEqualityCycleNodes_ι] using
    PolygonUniversalAction.node_act K (2 * s + 4) (by omega) N Q H a i

/-- The split-group identity acts as the identity on the whole original fiber. -/
theorem positiveEqualityCycleAction_unit : η[G] ▷ C ≫ A = (λ_ C).hom :=
  PolygonActionUnit.unit_act K (2 * s + 4) (by omega) N Q H

/-- The full original-fiber action satisfies the group multiplication law. -/
theorem positiveEqualityCycleAction_assoc :
    μ[G] ▷ C ≫ A = (α_ G G C).hom ≫ G ◁ A ≫ A :=
  PolygonActionAssociativity.assoc_act K (2 * s + 4) (by omega) N Q H

end FLT.Mazur.WeierstrassDividedDepth
