/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.StableAffineQuotientDescent

/-!
# Arbitrary-target descent through the affine invariant-coordinate quotient

The whole affine source is an invariant affine chart. Transporting along its
actual equivariant top-open isomorphism connects the constructed global descent
to the invariant-coordinate quotient, including uniqueness for every scheme target.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} [IsAffine X]
variable (ρ : G →* Aut X)

/-- The entire affine scheme is an actual invariant affine chart. -/
def affineTopChart : StableAffineQuotient.Chart ρ :=
  ⟨⊤, isAffineOpen_top X, fun _ ↦ by simp⟩

omit [Finite G] in
/-- The entire affine chart supplies the stable affine cover hypothesis. -/
theorem affineCharts_cover : ⨆ U : StableAffineQuotient.Chart ρ, U.val = ⊤ :=
  top_le_iff.mp (le_iSup_of_le (affineTopChart ρ) le_rfl)

/-- The quotient of the entire affine chart is the original invariant-coordinate quotient. -/
def affineTopQuotientIso :
    quotient (StableAffineQuotient.action ρ (affineTopChart ρ)) ≅ quotient ρ :=
  quotientIso _ ρ X.topIso
    (FiniteGroupRestriction.restrictedAction_hom_ι ρ ⊤ (affineTopChart ρ).property.2)

omit [Finite G] in
/-- The top-chart quotient identification preserves the actual quotient morphisms. -/
@[reassoc]
lemma affineTopQuotientIso_fac :
    quotientMap (StableAffineQuotient.action ρ (affineTopChart ρ)) ≫
      (affineTopQuotientIso ρ).hom = X.topIso.hom ≫ quotientMap ρ :=
  quotientMap_naturality _ _ _ _

variable {Y : Scheme.{u}} (f : X ⟶ Y) (hf : ∀ g : G, (ρ g).hom ≫ f = f)

/-- The actual descended morphism from the affine quotient to any scheme target. -/
def desc : quotient ρ ⟶ Y :=
  (affineTopQuotientIso ρ).inv ≫
    StableAffineQuotient.chartMap ρ (affineTopChart ρ) ≫
      StableAffineQuotient.desc ρ (affineCharts_cover ρ) f hf

/-- Arbitrary-target descent factors the original map as an equality of scheme morphisms. -/
@[reassoc]
lemma desc_fac : quotientMap ρ ≫ desc ρ f hf = f := by
  rw [← cancel_epi X.topIso.hom]
  unfold desc
  rw [← affineTopQuotientIso_fac_assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc]
  change StableAffineQuotient.localMap ρ (affineTopChart ρ) ≫ _ = _
  rw [← StableAffineQuotient.ι_map ρ (affineCharts_cover ρ) (affineTopChart ρ),
    Category.assoc, StableAffineQuotient.desc_fac]
  rfl

include hf in
/-- Every invariant map from an affine scheme factors uniquely through its quotient. -/
theorem existsUnique_desc : ∃! k : quotient ρ ⟶ Y, quotientMap ρ ≫ k = f := by
  refine ⟨desc ρ f hf, desc_fac ρ f hf, ?_⟩
  intro k hk
  rw [← cancel_epi (quotientMap ρ), hk, desc_fac]

/-- The affine invariant quotient has the categorical universal property for all scheme targets. -/
theorem invariant_iff_existsUnique_desc :
    (∀ g : G, (ρ g).hom ≫ f = f) ↔ ∃! k : quotient ρ ⟶ Y, quotientMap ρ ≫ k = f := by
  constructor
  · exact existsUnique_desc ρ f
  · rintro ⟨k, hk, _⟩ g
    rw [← hk, quotientMap_invariant_assoc]

end FLT.Mazur.SchemeFiniteGroupQuotient
