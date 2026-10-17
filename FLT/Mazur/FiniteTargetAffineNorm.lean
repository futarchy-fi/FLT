/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatGlobalSections
public import FLT.Mazur.FiniteProjectiveAffineNorm
public import FLT.Mazur.SchemeFiniteTargetRestriction

/-!
# Actual affine norms on the finite target locus

Every affine target open in the exact finite locus has a multiplicative norm
on its whole original preimage. Flat finite presentation constructs the local
bases. Neither global finiteness nor global affineness of the source is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteTargetAffineNorm
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} (p : D ⟶ A) [Flat p] [LocallyOfFinitePresentation p]
  (U : A.affineOpens) (hU : U.1 ≤ finiteTargetOpen p)

/-- The constructed norm of the entire original preimage of an affine finite target open. -/
def norm : Γ((p ⁻¹ᵁ U.1).toScheme, ⊤) →* Γ(U.1, ⊤) := by
  let _ := finite_restrict_of_le_finiteTarget p U.1 hU
  let _ : IsAffine (p ⁻¹ᵁ U.1).toScheme := isAffine_of_isAffineHom (p ∣_ U.1)
  exact FiniteProjectiveAffineNorm.norm (p ∣_ U.1) (p ∣_ U.1).finite_appTop
    (FCurve.finiteFlat_appTop_projective (p ∣_ U.1))

/-- Nonvanishing of the local norm tests the entire original restricted fiber. -/
theorem mem_basicOpen_norm_iff (s : Γ((p ⁻¹ᵁ U.1).toScheme, ⊤)) (x : U.1.toScheme) :
    x ∈ U.1.toScheme.basicOpen (norm p U hU s) ↔
      ∀ z : (p ⁻¹ᵁ U.1).toScheme, (p ∣_ U.1) z = x →
        z ∈ (p ⁻¹ᵁ U.1).toScheme.basicOpen s := by
  let _ := finite_restrict_of_le_finiteTarget p U.1 hU
  let _ : IsAffine (p ⁻¹ᵁ U.1).toScheme := isAffine_of_isAffineHom (p ∣_ U.1)
  exact FiniteProjectiveAffineNorm.mem_basicOpen_norm_iff (p ∣_ U.1)
    (p ∣_ U.1).finite_appTop (FCurve.finiteFlat_appTop_projective (p ∣_ U.1)) s x

end FLT.Mazur.FiniteTargetAffineNorm
