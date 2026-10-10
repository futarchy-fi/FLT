/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupClosureAffineGroup

/-!
# The Hopf algebra of the actual finite subgroup closure

Fully faithful affine spectrum reflects the constructed geometric group onto
the existing global coordinate algebra. The Hopf identities are inherited from
the proved group laws, and its algebra structure is the original one.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Functor Monoidal

namespace FLT.Mazur.EllipticSubgroupChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point) [hH : Finite H]
  [hA : IsDedekindDomain A]

/-- Reflect the actual affine group into the opposite category of the original algebras. -/
@[instance_reducible] def closureCoordinateGrpObj (hΔ : IsUnit W.Δ) :
    GrpObj (op (CommAlgCat.of A (GlobalClosure A W H))) := by
  letI := closureAffineGrpObj A W H hΔ
  letI : (algSpec (.of A)).Monoidal := braidedAlgSpec.toMonoidal
  exact (algSpec.fullyFaithful (R := .of A)).grpObj
    (op (CommAlgCat.of A (GlobalClosure A W H)))

/-- The actual finite closure coordinate algebra, with its constructed Hopf operations. -/
@[instance_reducible] def globalClosureHopfAlgebra (hΔ : IsUnit W.Δ) :
    HopfAlgebra A (GlobalClosure A W H) := by
  letI := closureCoordinateGrpObj A W H hΔ
  exact ((commHopfAlgCatEquivCogrpCommAlgCat A).inverse.obj
    (op (Grp.mk (op (CommAlgCat.of A (GlobalClosure A W H)))))).hopfAlgebra

/-- The Hopf construction retains the original structural algebra of the closure. -/
theorem globalClosureHopfAlgebra_toAlgebra (hΔ : IsUnit W.Δ) :
    (globalClosureHopfAlgebra A W H hΔ).toAlgebra = globalClosureAlgebra A W H := rfl

/-- The original finite flat global coordinate algebra bundled with its recovered operations. -/
def globalClosureHopf (hΔ : IsUnit W.Δ) : CommHopfAlgCat A := by
  letI := globalClosureHopfAlgebra A W H hΔ
  exact CommHopfAlgCat.of A (GlobalClosure A W H)

end FLT.Mazur.EllipticSubgroupChart
