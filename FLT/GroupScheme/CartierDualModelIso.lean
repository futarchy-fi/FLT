/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.GroupScheme.FiniteFlatIso
public import FLT.GroupScheme.CartierDualKernelInclusion

/-!
# Integral isomorphisms and Cartier duality

Cartier transpose takes an integral isomorphism to an isomorphism of the dual
models. The integral bidual comparison transports an identification of duals
back to the original models. In particular an identification of the dual with
`constantThree` identifies the original model with `muThree`.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan
namespace FiniteFlatObject

variable {R : Type} [CommRing R] [Algebra R ℚ] [IsDomain R] [IsPrincipalIdealRing R]

/-- Cartier transpose reverses integral isomorphisms of finite-flat objects. -/
def Iso.cartierDual {H J : FiniteFlatObject R} (e : H.Iso J) :
    J.cartierDual.Iso H.cartierDual := by
  change HopfAlgebra.CartierDual R H.model.CoordinateRing ≃ₐc[R]
    HopfAlgebra.CartierDual R J.model.CoordinateRing
  refine BialgEquiv.ofBialgHom
    (HopfAlgebra.CartierDual.bialgMap e.toBialgHom)
    (HopfAlgebra.CartierDual.bialgMap e.symm.toBialgHom) ?_ ?_
  · ext φ a
    change φ (e.symm (e a)) = φ a
    rw [e.symm_apply_apply]
  · ext φ a
    change φ (e (e.symm a)) = φ a
    rw [e.apply_symm_apply]

/-- An integral identification of dual models identifies the original models by biduality. -/
def Iso.ofCartierDual {H J : FiniteFlatObject R} (e : H.cartierDual.Iso J.cartierDual) :
    H.Iso J :=
  J.cartierBidualEquiv.symm.trans (e.cartierDual.symm.trans H.cartierBidualEquiv)

end FiniteFlatObject

/-- Identifying the integral dual with the constant-three model identifies the original
model with the cube-root model. The induced point map is built into the integral isomorphism. -/
def isoMuThreeOfDualConstant (H : FiniteFlatObject ZInvTwo)
    (e : H.cartierDual.Iso constantThree) : H.Iso muThree :=
  FiniteFlatObject.Iso.ofCartierDual (muThreeCartierDualEquiv.trans e)

end ThreeAdicPlan
