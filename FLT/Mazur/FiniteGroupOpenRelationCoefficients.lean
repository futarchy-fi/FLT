/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupEquivariantOpenBoundary

/-!
# Moving coefficients from arbitrary invariant open domains

An action whose transitions lie in an original relation preserves every
equalized function on an invariant open of that relation. The function need
not extend to the entire original source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteGroupOpenRelation
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type} [Group G] {X B C : Scheme}
  (ρ : G →* Aut X) (b : X ⟶ B) (r s : C ⟶ B) (z : G → (X ⟶ C))
  (hr : ∀ g, z g ≫ r = b) (hs : ∀ g, z g ≫ s = (ρ g).hom ≫ b)
  (V : B.Opens) (hV : r ⁻¹ᵁ V = s ⁻¹ᵁ V)
  (U : X.Opens) (hU : ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) (hUV : U ≤ b ⁻¹ᵁ V)

/-- The endpoint on the actual open where the original coefficient is defined. -/
def openEndpoint : U.toScheme ⟶ V.toScheme := b.resLE V U hUV

omit [Group G] in
include hr hUV in
/-- Every original transition stays in the full relation over the coefficient domain. -/
theorem transition_open_le (g : G) : U ≤ z g ⁻¹ᵁ (r ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, hr]
  exact hUV

/-- Restrict the original transition without selecting a smaller arrow relation. -/
def openTransition (g : G) : U.toScheme ⟶ (r ⁻¹ᵁ V).toScheme :=
  (z g).resLE (r ⁻¹ᵁ V) U (transition_open_le b r z hr V U hUV g)

omit [Group G] in
/-- The first restricted endpoint is the actual coefficient-domain map. -/
@[reassoc] theorem openTransition_first (g : G) :
    openTransition b r z hr V U hUV g ≫ (r ∣_ V) = openEndpoint b V U hUV := by
  apply (cancel_mono V.ι).mp
  rw [Category.assoc, morphismRestrict_ι]
  change _ = b.resLE V U hUV ≫ V.ι
  rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc]
  change ((z g).resLE (r ⁻¹ᵁ V) U _ ≫ (r ⁻¹ᵁ V).ι) ≫ r = _
  rw [Scheme.Hom.resLE_comp_ι, Category.assoc, hr]

include hs in
/-- The second restricted endpoint follows the moving action on the source chart. -/
@[reassoc] theorem openTransition_second (g : G) :
    openTransition b r z hr V U hUV g ≫ s.resLE V _ hV.le =
      (restrictedAction ρ U hU g).hom ≫ openEndpoint b V U hUV := by
  apply (cancel_mono V.ι).mp
  simp only [openTransition, openEndpoint, Category.assoc,
    Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
    restrictedAction_hom_ι_assoc, hs]

variable (t : Γ(V.toScheme, ⊤))
  (ht : (r ∣_ V).appTop t = (s.resLE V _ hV.le).appTop t)

include hr hs ht in
/-- Equalization by the whole original open relation implies invariance on the moving chart. -/
theorem coefficient_invariant (g : G) :
    (restrictedAction ρ U hU g).hom.appTop ((openEndpoint b V U hUV).appTop t) =
      (openEndpoint b V U hUV).appTop t := by
  change (((openEndpoint b V U hUV).appTop ≫
    (restrictedAction ρ U hU g).hom.appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, ← openTransition_second ρ b r s z hr hs V hV U hU hUV]
  rw [Scheme.Hom.comp_appTop]
  change (openTransition b r z hr V U hUV g).appTop
    ((s.resLE V _ hV.le).appTop t) = _
  rw [← ht]
  change (((r ∣_ V).appTop ≫ (openTransition b r z hr V U hUV g).appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, openTransition_first]

/-- The coefficient constructed from a section defined only on its original open domain. -/
def invariantCoefficient : invariantCoordinates (restrictedAction ρ U hU) := by
  let _ := SchemeCoordinateAction.coordinateAction (restrictedAction ρ U hU)
  refine ⟨(openEndpoint b V U hUV).appTop t, ?_⟩
  intro g
  exact coefficient_invariant ρ b r s z hr hs V hV U hU hUV t ht g⁻¹

/-- No extension outside the original coefficient domain enters this construction. -/
theorem invariantCoefficient_val :
    (invariantCoefficient ρ b r s z hr hs V hV U hU hUV t ht).val =
      (b.resLE V U hUV).appTop t := rfl

end FLT.Mazur.FiniteGroupOpenRelation
