/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupClosureGroup
public import FLT.Mazur.EllipticSubgroupGlobalRank
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# The closure group on its original affine coordinate algebra

The affine comparison uses the already constructed valuation-ring algebra,
so transporting the actual closure group retains that structural algebra map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [Finite H]

/-- The actual affine coordinate comparison over the original valuation-ring algebra map. -/
def closureAffineOverIso : Over.mk (closureToBase A W H 1 2) ≅
    (algSpec (.of A)).obj (op (CommAlgCat.of A (GlobalClosure A W H))) :=
  Over.isoMk (gluedClosure A W H 1 2).isoSpec (globalClosure_toBase A W H)

/-- The affine comparison is precisely the original global-sections comparison. -/
theorem closureAffineOverIso_hom_left :
    (closureAffineOverIso A W H).hom.left = (gluedClosure A W H 1 2).isoSpec.hom := rfl

variable [IsDedekindDomain A]

/-- The actual group structure transported to the spectrum of the existing coordinate algebra. -/
@[instance_reducible] def closureAffineGrpObj (hΔ : IsUnit W.Δ) :
    GrpObj ((algSpec (.of A)).obj (op (CommAlgCat.of A (GlobalClosure A W H)))) := by
  letI := closureCommGrpObj A W H hΔ
  exact GrpObj.ofIso (closureAffineOverIso A W H)

/-- The affine comparison is an actual isomorphism of group objects. -/
def closureAffineGroupIso (hΔ : IsUnit W.Δ) :
    letI := closureAffineGrpObj A W H hΔ
    (closureGroup A W H hΔ).toGrp ≅
      Grp.mk ((algSpec (.of A)).obj (op (CommAlgCat.of A (GlobalClosure A W H)))) := by
  letI := closureCommGrpObj A W H hΔ
  letI := closureAffineGrpObj A W H hΔ
  exact Grp.mkIso' (closureAffineOverIso A W H)

end FLT.Mazur.EllipticSubgroupChart
