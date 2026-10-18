/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundarySubgroupIso
public import FLT.Mazur.GeneralizedCurveBaseChangeCoherence
public import FLT.Mazur.PolygonCompleteBoundaryCartesian

/-!
# The original whole-curve map in the boundary subgroup comparison

The compatible subgroup isomorphism has exactly the original Cartesian map
into the complete smoothing. In particular its subgroup comparison retains
the actual complete-family closed embedding, not just an abstract carrier.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "F" => completeGeneralizedCurve K n h
local notation "H" => completeOriginalFiniteSubgroup K n h
local notation "J" => completeClosedFiniteSubgroup K n h
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "b" => completeClosedBase K
local notation "e" => completeBoundarySubgroupIso K n h g

/-- The curve part is the original closed comparison with its canonical pullback comparison. -/
theorem completeBoundarySubgroupIso_curve :
    (e).curve = (F).baseChangeCompIso b g ≪≫
      (baseChangeFunctor g).mapIso (completeClosedCurveIso K n h).symm := by
  change (F).baseChangeCompIso b g ≪≫
    (baseChangeFunctor g).mapIso (completeClosedSubgroupIso K n h).curve = _
  rw [completeClosedSubgroupIso_curve]

/-- The inverse compatible comparison retains the exact whole-curve recovery map. -/
@[reassoc] theorem completeBoundarySubgroupIso_inv_fst :
    (e).curve.inv.curve.left ≫ pullback.fst (F).curve.hom (g ≫ b) =
      completeBoundaryParameterMap K n h g := by
  rw [completeBoundarySubgroupIso_curve, Iso.trans_inv]
  change ((baseChangeMap g (completeClosedCurveIso K n h).hom).curve.left ≫
    ((F).baseChangeCompIso b g).inv.curve.left) ≫ _ = _
  rw [Category.assoc, ← baseChangeCompIso_fst_fst F b g, ← Category.assoc
    ((F).baseChangeCompIso b g).inv.curve.left]
  have hi := congrArg (fun f => f.curve.left) ((F).baseChangeCompIso b g).inv_hom_id
  change ((F).baseChangeCompIso b g).inv.curve.left ≫
    ((F).baseChangeCompIso b g).hom.curve.left = 𝟙 _ at hi
  rw [hi, Category.id_comp, ← Category.assoc, baseChangeMap_fst, Category.assoc,
    completeClosedCurveIso_fst]
  rfl

/-- The subgroup comparison retains its original embedding into the complete smoothing. -/
@[reassoc] theorem completeBoundarySubgroupIso_subgroup_fst :
    (e).subgroup.inv.left ≫ ((H).baseChange (g ≫ b)).curveMap.left ≫
      pullback.fst (F).curve.hom (g ≫ b) =
        ((J).baseChange g).curveMap.left ≫ completeBoundaryParameterMap K n h g := by
  have hc := congrArg (fun f => f.left) (e).symm.compatible
  change ((J).baseChange g).curveMap.left ≫ (e).curve.inv.curve.left =
    (e).subgroup.inv.left ≫ ((H).baseChange (g ≫ b)).curveMap.left at hc
  rw [← Category.assoc, ← hc, Category.assoc, completeBoundarySubgroupIso_inv_fst]

end FLT.Mazur.PolygonInfinitesimalStages
