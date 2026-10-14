/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointOriginalBaseGroup
public import FLT.Mazur.PolygonCompletePointIdentityGeneric

/-!
# The original identity-open contraction is a group isomorphism

The transported group retains the original smooth cubic isomorphism. On every
nonzero-parameter field square the whole original curve lifts to this identity
open, with its actual contraction and marking unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "U" => completePointIdentityOpen K n h i

/-- The original smooth contraction preserves the constructed identity group law. -/
def completePointIdentityCubicGroupIso :
    completePointIdentityGroup K n h i ≅ integralSmoothGroup W := by
  let _ := integralSmoothCommGrpObj W
  let _ := completePointIdentityCommGrp K n h i
  let e := completePointIdentityOverIso K n h i
  let _ : IsMonHom e.inv := isMonHom_ofIso e.symm
  let _ : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  exact CommGrp.mkIso' e

/-- The group comparison retains the unchanged smooth contraction. -/
theorem completePointIdentityCubicGroupIso_hom :
    (completePointIdentityCubicGroupIso K n h i).hom.hom.hom.hom.left =
      (completePointSmoothCubicIso K n h i).hom := rfl

/-- Its inverse retains the unchanged inverse smooth contraction. -/
theorem completePointIdentityCubicGroupIso_inv :
    (completePointIdentityCubicGroupIso K n h i).inv.hom.hom.hom.left =
      (completePointSmoothCubicIso K n h i).inv := rfl

variable (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  {Y : Scheme} (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ Spec (.of L))
  (hs : IsPullback p q (exactVeroneseProjToBase K n h)
    (Spec.map (CommRingCat.ofHom a)))

/-- The whole original field square factors through the full original identity open. -/
def completePointFieldToIdentity : Y ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι p (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact (completePointIdentityOpen_field_preimage K n h i L a ha p q hs).ge
      (show x ∈ ⊤ from trivial))

/-- The lifted generic morphism is still the original Cartesian family projection. -/
@[reassoc] theorem completePointFieldToIdentity_inclusion :
    completePointFieldToIdentity K n h i L a ha p q hs ≫ (U).ι = p :=
  IsOpenImmersion.lift_fac _ _ _

/-- Its smooth cubic coordinate is the original complete contraction restricted to the field. -/
@[reassoc] theorem completePointFieldToIdentity_cubic :
    completePointFieldToIdentity K n h i L a ha p q hs ≫
      (completePointSmoothCubicIso K n h i).hom ≫ (integralSmoothOpen W).ι =
        p ≫ completePointToIntegralCubic K n h i := by
  rw [completePointSmoothCubicIso_inclusion, completePointFieldToIdentity_inclusion_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
