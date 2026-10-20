/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafPowerPullback
public import FLT.Mazur.IdealSheafClosedTransitions

/-!
# Exact errors on original affine test schemes

Pulling an original affine representative to a test scheme commutes with the
full closed reduction. Equality after that reduction gives membership in the
actual pulled ideal power, with no reduced-support replacement.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.IdealSheafAffineTestErrors
set_option backward.isDefEq.respectTransparency false
variable {X Y T : Scheme.{0}} [IsAffine T]
  (I : X.IdealSheafData) (K : T.IdealSheafData) (n : ℕ)
  (U : X.affineOpens) (g : T ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1)
  (a : (K ^ n).subscheme ⟶ (I ^ n).subscheme)
  (ha : a ≫ (I ^ n).subschemeι = (K ^ n).subschemeι ≫ g)

omit [IsAffine T] in
include hg ha in
/-- The entire closed test source maps into the chosen affine reduction domain. -/
theorem closed_domain : ⊤ ≤ a ⁻¹ᵁ ((I ^ n).subschemeι ⁻¹ᵁ U.1) := by
  change ⊤ ≤ (a ≫ (I ^ n).subschemeι) ⁻¹ᵁ U.1
  rw [ha]
  exact le_trans (by simp) ((TopologicalSpace.Opens.map
    (K ^ n).subschemeι.base).monotone hg)

omit [IsAffine T] in
/-- Evaluation of a representative and closed reduction commute on the full test scheme. -/
theorem representative_restrict (w : Γ(X, U.1)) :
    (K ^ n).subschemeι.appTop (g.appLE U.1 ⊤ hg w) =
      a.appLE ((I ^ n).subschemeι ⁻¹ᵁ U.1) ⊤
        (closed_domain I K n U g hg a ha) ((I ^ n).subschemeι.app U.1 w) := by
  have he : g.appLE U.1 ⊤ hg ≫ (K ^ n).subschemeι.appTop =
      (I ^ n).subschemeι.app U.1 ≫
        a.appLE ((I ^ n).subschemeι ⁻¹ᵁ U.1) ⊤
          (closed_domain I K n U g hg a ha) := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE (K ^ n).subschemeι,
      Scheme.Hom.appLE_comp_appLE, ← Scheme.Hom.comp_appLE]
    simp only [ha, Scheme.Hom.preimage_top]
  exact congrArg (fun r ↦ r w) he

/-- A prescribed test value and a representative differ by the full ideal power. -/
theorem representative_error (w : Γ(X, U.1)) (v : Γ(T, ⊤))
    (h : a.appLE ((I ^ n).subschemeι ⁻¹ᵁ U.1) ⊤
      (closed_domain I K n U g hg a ha) ((I ^ n).subschemeι.app U.1 w) =
        (K ^ n).subschemeι.appTop v) :
    g.appLE U.1 ⊤ hg w - v ∈ (K.ideal ⟨⊤, isAffineOpen_top T⟩) ^ n := by
  change _ ∈ (K ^ n).ideal ⟨⊤, isAffineOpen_top T⟩
  rw [← (K ^ n).ker_subschemeι_app]
  change (K ^ n).subschemeι.app ⊤ _ = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((representative_restrict I K n U g hg a ha w).trans h)

/-- The canonical closed test map uses the pulled ideal, before taking its power. -/
def pulledMap : ((I.comap g) ^ n).subscheme ⟶ (I ^ n).subscheme :=
  IdealSheafClosedTransitions.map _ _ g (IdealSheafPowerPullback.comap_pow I g n)

omit [IsAffine T] in
/-- Its defining square retains the unchanged original test morphism. -/
@[reassoc]
theorem pulledMap_inclusion :
    pulledMap I n g ≫ (I ^ n).subschemeι = ((I.comap g) ^ n).subschemeι ≫ g :=
  IdealSheafClosedTransitions.map_inclusion _ _ _ _

end FLT.Mazur.IdealSheafAffineTestErrors
