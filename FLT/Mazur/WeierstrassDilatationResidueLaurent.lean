/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationResidueGeometry

/-!
# The entire middle divided residue chart is a Laurent scheme

The comparison is over the residue field and covers the whole actual tensor
fiber. In particular its structure morphism is smooth, including every point.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDilatation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)
  (k : ℕ) (hk0 : 0 < k) (hk : 2 * k ≤ n) (b3 b4 b6 : R)
  (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4)
  (h6 : W.a₆ = (π ^ k) ^ 2 * b6) (hmiddle : 2 * k = n)
local notation "K" => ResidueField R

/-- The Laurent scheme is the entire tensor fiber at exact middle depth. -/
def residueLaurentIso : Spec (.of (K[T;T⁻¹])) ≅
    Spec (.of (ScalarExtension W (π ^ k) b3 b4 b6 K)) :=
  Scheme.Spec.mapIso
    (residueLaurentEquiv D k hk0 hk b3 b4 b6 h3 h4 h6 hmiddle).toRingEquiv.toCommRingCatIso.op

/-- The whole middle chart comparison preserves the residue-field structure. -/
@[reassoc] theorem residueLaurentIso_structure :
    (residueLaurentIso D k hk0 hk b3 b4 b6 h3 h4 h6 hmiddle).hom ≫
      residueStructure k b3 b4 b6 = (MultiplicativeGroupScheme.gm K).hom :=
  algebraSpecIso_structure _

include D hk0 hk h3 h4 h6 hmiddle in
/-- Every point of the entire exact-middle tensor chart is smooth over the residue field. -/
theorem residueStructure_smooth_of_middle :
    Smooth (residueStructure (W := W) (π := π) k b3 b4 b6) := by
  let e := residueLaurentIso D k hk0 hk b3 b4 b6 h3 h4 h6 hmiddle
  have h : e.hom ≫ residueStructure k b3 b4 b6 =
      (MultiplicativeGroupScheme.gm K).hom := residueLaurentIso_structure ..
  have he : residueStructure k b3 b4 b6 = e.inv ≫ (MultiplicativeGroupScheme.gm K).hom := by
    rw [← h, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [he]
  have := MultiplicativeGroupScheme.smooth K
  infer_instance

end FLT.Mazur.WeierstrassDilatation
