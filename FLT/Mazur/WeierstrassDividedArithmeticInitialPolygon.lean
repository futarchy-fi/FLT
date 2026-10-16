/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialPolygonTransport
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledSystem
public import FLT.Mazur.PolygonArithmeticSystem

/-!
# The original initial labels map naturally to the polygon at starting depth one

The starting depth is explicitly one, so the original smoothing π^start is π.
For larger starting depths the thick comparison remains available separately.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k : ℕ) (hk : k ≤ n)

/-- Both original initial labels map to their specified full polygon opens at starting depth one. -/
def arithmeticInitialPolygonMap (m : ℕ) (b : Bool) :
    arithmeticLabeledAtlasObject hπ data H m k hk (.initial b) ⟶
      (family R π m (2 * k + 3) (by omega)).left :=
  initialPolygonMapOfEq (W.map (algebraMap R (Quotient R π m)))
    (algebraMap R (Quotient R π m) (π ^ 1)) (parameter R π m)
    (by rw [pow_one]; rfl) k b

attribute [local irreducible] initialPolygonMapOfEq

instance arithmeticInitialPolygonMap_isOpenImmersion (m : ℕ) (b : Bool) :
    IsOpenImmersion (arithmeticInitialPolygonMap hπ data H k hk m b) := by
  dsimp only [arithmeticInitialPolygonMap]
  infer_instance

omit [IsBezout R] in
/-- Each original initial quotient restriction commutes with its specific polygon map. -/
@[reassoc] theorem arithmeticInitialPolygonMap_restriction (m : ℕ) (b : Bool) :
    arithmeticLabeledAtlasRestriction hπ data H m k hk (.initial b) ≫
      arithmeticInitialPolygonMap hπ data H k hk (m + 1) b =
    arithmeticInitialPolygonMap hπ data H k hk m b ≫
      stageRestriction R π m (2 * k + 3) (by omega) :=
  (initialPolygonMapOfEq_parameterProjection
    (W.map (algebraMap R (Quotient R π (m + 1))))
    (algebraMap R (Quotient R π (m + 1)) (π ^ 1)) (parameter R π (m + 1))
    (by rw [pow_one]; rfl) k (restriction R π m).toRingHom
    (W.map (algebraMap R (Quotient R π m)))
    (algebraMap R (Quotient R π m) (π ^ 1)) (parameter R π m)
    (arithmeticInitialCurve_restriction R π m W) ((restriction R π m).commutes (π ^ 1))
    (restriction_parameter R π m) (by rw [pow_one]; rfl) b).symm

attribute [local irreducible] arithmeticInitialPolygonMap

/-- Both full original initial chart systems have natural comparisons to the complete polygon. -/
def arithmeticInitialPolygonSystem (b : Bool) :
    arithmeticLabeledChartSystem hπ data H k hk (.initial b) ⟶
      stageSystem R π (2 * k + 3) (by omega) :=
  NatTrans.ofSequence (fun m ↦ arithmeticInitialPolygonMap hπ data H k hk m b) (by
    intro m
    simpa only [arithmeticLabeledChartSystem, stageSystem, Functor.ofSequence_obj,
      Functor.ofSequence_map_homOfLE_succ] using
        arithmeticInitialPolygonMap_restriction hπ data H k hk m b)

omit [IsBezout R] in
/-- The two initial comparisons preserve every original nonadjacent quotient arrow. -/
@[reassoc] theorem arithmeticInitialPolygonSystem_naturality (b : Bool)
    {a c : ℕ} (hac : a ≤ c) :
    (arithmeticLabeledChartSystem hπ data H k hk (.initial b)).map (homOfLE hac) ≫
      arithmeticInitialPolygonMap hπ data H k hk c b =
    arithmeticInitialPolygonMap hπ data H k hk a b ≫
      (stageSystem R π (2 * k + 3) (by omega)).map (homOfLE hac) :=
  (arithmeticInitialPolygonSystem hπ data H k hk b).naturality (homOfLE hac)

end FLT.Mazur.WeierstrassDividedDepth
