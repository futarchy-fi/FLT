/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupQuotientIso
public import FLT.Mazur.SchemeFiniteGroupInvariantPrincipal

/-!
# Equivariant comparison of principal charts

A principal open contained in the image of an equivariant open immersion
is isomorphic to its inverse image. The isomorphism intertwines the actual
restricted actions, and hence identifies their invariant-coordinate quotients.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] {X Y : Scheme.{u}}
variable (ρ : G →* Aut X) (τ : G →* Aut Y)
variable (f : X ⟶ Y) [IsOpenImmersion f]
variable (hf : ∀ g : G, (ρ g).hom ≫ f = f ≫ (τ g).hom)
variable (r : invariantCoordinates τ)
variable (hr : (Y.basicOpen (r : Γ(Y, ⊤)) : Set Y) ⊆ Set.range f)

include hr

omit [IsOpenImmersion f] in
/-- Pullback identifies the principal chart with its full image in the target. -/
lemma principal_chart_range :
    Set.range ((X.basicOpen (invariantMap ρ τ f hf r : Γ(X, ⊤))).ι ≫ f) =
      Set.range (Y.basicOpen (r : Γ(Y, ⊤))).ι := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    Scheme.Opens.range_ι]
  change f '' (X.basicOpen (f.appTop.hom (r : Γ(Y, ⊤))) : Set X) = _
  rw [← Scheme.preimage_basicOpen_top]
  exact Set.image_preimage_eq_of_subset hr

/-- The actual isomorphism between the source and target principal charts. -/
def principalChartIso :
    (X.basicOpen (invariantMap ρ τ f hf r : Γ(X, ⊤))).toScheme ≅
      (Y.basicOpen (r : Γ(Y, ⊤))).toScheme :=
  IsOpenImmersion.isoOfRangeEq _ _ (principal_chart_range ρ τ f hf r hr)

/-- The chart comparison is the restriction of the original map. -/
@[reassoc]
lemma principalChartIso_hom_ι :
    (principalChartIso ρ τ f hf r hr).hom ≫ (Y.basicOpen (r : Γ(Y, ⊤))).ι =
      (X.basicOpen (invariantMap ρ τ f hf r : Γ(X, ⊤))).ι ≫ f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The chart comparison intertwines the constructed restricted actions. -/
lemma principalChartIso_equivariant (g : G) :
    (principalAction ρ (invariantMap ρ τ f hf r) g).hom ≫
        (principalChartIso ρ τ f hf r hr).hom =
      (principalChartIso ρ τ f hf r hr).hom ≫ (principalAction τ r g).hom := by
  apply (cancel_mono (Y.basicOpen (r : Γ(Y, ⊤))).ι).mp
  simp only [Category.assoc, principalChartIso_hom_ι, principal_ι_equivariant]
  rw [← Category.assoc, principal_ι_equivariant, Category.assoc, hf g,
    ← principalChartIso_hom_ι_assoc]

/-- Principal chart comparison descends to an actual scheme isomorphism. -/
def principalQuotientIso :
    quotient (principalAction ρ (invariantMap ρ τ f hf r)) ≅
      quotient (principalAction τ r) :=
  quotientIso _ _ (principalChartIso ρ τ f hf r hr)
    (principalChartIso_equivariant ρ τ f hf r hr)

/-- The principal quotient comparison commutes with the ambient quotient maps. -/
@[reassoc]
lemma principalQuotientIso_hom_map :
    (principalQuotientIso ρ τ f hf r hr).hom ≫ principalQuotientMap τ r =
      principalQuotientMap ρ (invariantMap ρ τ f hf r) ≫ quotientHom ρ τ f hf := by
  change quotientHom _ _ _ _ ≫ quotientHom _ _ _ _ =
    quotientHom _ _ _ _ ≫ quotientHom _ _ _ _
  rw [quotientHom_comp _ _ _ _ _ _ _ (fun g ↦ by
    simp only [Category.assoc, principalChartIso_hom_ι, principal_ι_equivariant_assoc,
      hf g]), quotientHom_comp _ _ _ _ _ _ _ (fun g ↦ by
    rw [principal_ι_equivariant_assoc, Category.assoc, hf g])]
  congr 1
  exact principalChartIso_hom_ι ρ τ f hf r hr

end FLT.Mazur.SchemeFiniteGroupQuotient
