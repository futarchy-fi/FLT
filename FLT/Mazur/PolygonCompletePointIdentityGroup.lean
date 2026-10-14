/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointSmoothIso
public import FLT.Mazur.WeierstrassSmoothGroup

/-!
# The original identity open carries the full smooth cubic group

Transport the established cubic law through the actual restricted contraction.
The carrier is an open of the original complete polygon; its group identity
is the original chosen marking, with the specified coefficient identification.
This constructs the identity open's group, not yet the whole smooth polygon.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "c" => integralCurveStructure (W)
local notation "s" => completeBaseMarking K n h i

/-- The entire inverse image of the smooth cubic in the original complete polygon. -/
abbrev completePointIdentityOpen : (exactVeroneseProj K n h).Opens :=
  (g) ⁻¹ᵁ (c).smoothLocus

local notation "U" => completePointIdentityOpen K n h i
attribute [local instance] exactVeroneseProjToBase_lfp

/-- The constructed identity open lies in the original family's actual relative smooth locus. -/
theorem completePointIdentityOpen_le_smooth :
    (U) ≤ (exactVeroneseProjToBase K n h).smoothLocus := by
  let _ := exactVeroneseProjToBase_lfp K n h
  have he : (U).ι ≫ exactVeroneseProjToBase K n h =
      (completePointSmoothCubicIso K n h i).hom ≫
        integralSmoothStructure (W) ≫ inv (S₀).toSpecΓ := by
    simp only [integralSmoothStructure, Category.assoc,
      completePointSmoothCubicIso_inclusion_assoc, completePointToIntegralCubic_over_assoc,
      IsIso.hom_inv_id, Category.comp_id]
  let _ : Smooth ((U).ι ≫ exactVeroneseProjToBase K n h) := by
    rw [he]
    infer_instance
  have hl := Scheme.Hom.preimage_smoothLocus_eq (U).ι (exactVeroneseProjToBase K n h)
  rw [Scheme.Hom.smoothLocus_eq_top ((U).ι ≫ exactVeroneseProjToBase K n h)] at hl
  intro x hx
  exact hl.ge (show (⟨x, hx⟩ : (U).toScheme) ∈ ⊤ from trivial)

/-- The original identity open over the actual cubic coefficient spectrum. -/
def completePointIdentityOver : Over (Spec (.of Γ(S₀, ⊤))) :=
  Over.mk ((U).ι ≫ (g) ≫ (c))

/-- The actual contraction identifies this entire original open with the smooth cubic. -/
def completePointIdentityOverIso :
    completePointIdentityOver K n h i ≅ integralSmoothOver (W) :=
  Over.isoMk (completePointSmoothCubicIso K n h i)
    (by exact completePointSmoothCubicIso_inclusion_assoc K n h i (c))

/-- The identity open has a constructed commutative group law over the complete base. -/
abbrev completePointIdentityCommGrp : CommGrpObj (completePointIdentityOver K n h i) := by
  let _ := integralSmoothCommGrpObj (W)
  refine
    { __ := GrpObj.ofIso (completePointIdentityOverIso K n h i).symm
      mul_comm := ?_ }
  change (β_ _ _).hom ≫
    ((completePointIdentityOverIso K n h i).hom ⊗ₘ
      (completePointIdentityOverIso K n h i).hom) ≫
        MonObj.mul ≫ (completePointIdentityOverIso K n h i).inv = _
  rw [← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm_assoc]
  rfl

/-- The proved commutative group on the original identity open, bundled. -/
def completePointIdentityGroup : CommGrp (Over (Spec (.of Γ(S₀, ⊤)))) := by
  let _ := completePointIdentityCommGrp K n h i
  exact ⟨completePointIdentityOver K n h i⟩

/-- The original marking lies on the entire original identity open. -/
theorem completeBaseMarking_range_identityOpen : Set.range (s) ⊆ (U) := by
  rintro _ ⟨x, rfl⟩
  change ((s) ≫ (g)) x ∈ integralSmoothOpen (W)
  rw [completePointToIntegralCubic_marking]
  exact integralCurveZero_range_smooth (W) ⟨_, rfl⟩

/-- The original complete-base marking lifted to the proved identity open. -/
def completePointIdentityMarking : S₀ ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι (s)
    (by rw [Scheme.Opens.range_ι]; exact completeBaseMarking_range_identityOpen K n h i)

/-- The lifted identity marking retains its original whole-family inclusion. -/
@[reassoc] theorem completePointIdentityMarking_inclusion :
    completePointIdentityMarking K n h i ≫ (U).ι = (s) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The original marking maps to the smooth cubic's actual zero section. -/
@[reassoc] theorem completePointIdentityMarking_toSmooth :
    completePointIdentityMarking K n h i ≫ (completePointSmoothCubicIso K n h i).hom =
      (S₀).toSpecΓ ≫ integralSmoothZero (W) := by
  apply (cancel_mono (integralSmoothOpen (W)).ι).mp
  rw [Category.assoc, completePointSmoothCubicIso_inclusion,
    completePointIdentityMarking_inclusion_assoc, Category.assoc, integralSmoothZero_inclusion,
    completePointToIntegralCubic_marking]

/-- The transported group's identity is precisely the unchanged original marked section. -/
theorem completePointIdentityCommGrp_identity :
    let _ := completePointIdentityCommGrp K n h i
    (η[completePointIdentityOver K n h i]).left =
      inv (S₀).toSpecΓ ≫ completePointIdentityMarking K n h i := by
  let _ := integralSmoothCommGrpObj (W)
  let _ := completePointIdentityCommGrp K n h i
  apply (cancel_mono (completePointSmoothCubicIso K n h i).hom).mp
  change (integralSmoothZero (W) ≫ (completePointSmoothCubicIso K n h i).inv) ≫
    (completePointSmoothCubicIso K n h i).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, completePointIdentityMarking_toSmooth,
    IsIso.inv_hom_id_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
