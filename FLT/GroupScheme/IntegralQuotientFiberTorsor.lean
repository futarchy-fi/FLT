/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.IntegralQuotientPointFiber
public import FLT.GroupScheme.HopfPointFiberTorsor

/-!
# The torsor comparison on the contracted integral quotient fibre

The finite faithfully flat fibre constructed from the actual generic quotient
now carries the canonical comparison and coaction of its augmentation kernel.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsDedekindDomain R] [IsFractionRing R K]
  [IsPrincipalIdealRing R] {X Q : FF R K}
  (q : GenericGaloisHom X Q) (p : q.quotientCoordinates →ₐ[R] R)

/-- The canonical comparison on the actual finite faithfully flat point fibre. -/
def quotientPointFiberTorsorEquiv :
    QuotientPointFiber q p ⊗[R] QuotientPointFiber q p ≃ₐ[QuotientPointFiber q p]
      QuotientPointFiber q p ⊗[R]
        (X.CoordinateRing ⧸ HopfAlgebra.augmentationIdeal q.quotientInclusion) :=
  HopfAlgebra.pointFiberTorsorEquiv q.quotientInclusion (by ext; rfl) p

/-- The augmentation-kernel coaction on the constructed quotient fibre. -/
def quotientPointFiberCoaction : QuotientPointFiber q p →ₐ[R]
    QuotientPointFiber q p ⊗[R]
      (X.CoordinateRing ⧸ HopfAlgebra.augmentationIdeal q.quotientInclusion) :=
  HopfAlgebra.pointFiberCoaction q.quotientInclusion (by ext; rfl) p

omit [IsPrincipalIdealRing R] in
/-- On middle coordinates the fibre coaction is exactly the Hopf coaction. -/
theorem quotientPointFiberCoaction_map (a : X.CoordinateRing) :
    quotientPointFiberCoaction q p (HopfAlgebra.pointFiberMap p a) =
      Algebra.TensorProduct.map (HopfAlgebra.pointFiberMap p)
        (AlgHom.id R (X.CoordinateRing ⧸ HopfAlgebra.augmentationIdeal q.quotientInclusion))
        (HopfAlgebra.torsorCoaction q.quotientInclusion a) :=
  HopfAlgebra.pointFiberCoaction_map q.quotientInclusion (by ext; rfl) p a

end ThreeAdicPlan
