/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundarySubframe

/-!
# Original open boundary coefficients under mixed-size selection

The full invariant domain of any original boundary section is preserved by
subframe selection. Its coefficients agree on that entire inverse image, without
extending the section globally or replacing the closed scheme by its reduction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J) (ι : J ↪ I)
  (i : B ⟶ A) [Mono i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
  (V : B.Opens) (hV : r ⁻¹ᵁ V = s ⁻¹ᵁ V)
local notation "b₁" => endpoint (p := p) (q := q) I o i
local notation "b₂" => endpoint (p := p) (q := q) J o' i
local notation "t₀" => labelTransition (q := q) I o (ι o') i z r hr
local notation "l" => subframeBoundaryMap e o o' i z r s hr hs ι

include hV in
omit [Mono i] in
/-- The full original coefficient domain is preserved by mixed-size closed subframe selection. -/
theorem subframeBoundaryMap_domain : (l) ⁻¹ᵁ ((b₂) ⁻¹ᵁ V) = (b₁) ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, subframeBoundaryMap_endpoint, Scheme.Hom.comp_preimage, ← hV,
    ← Scheme.Hom.comp_preimage, labelTransition_first]

/-- The subframe morphism restricted to the entire inverse image coefficient domain. -/
def subframeDomainMap : ((b₁) ⁻¹ᵁ V).toScheme ⟶ ((b₂) ⁻¹ᵁ V).toScheme :=
  (l).resLE ((b₂) ⁻¹ᵁ V) ((b₁) ⁻¹ᵁ V) (subframeBoundaryMap_domain e o o' ι i z r s hr hs V hV).ge

/-- The actual original closed subframe arrow over the original section's open domain. -/
def subframeDomainTransition : ((b₁) ⁻¹ᵁ V).toScheme ⟶ (r ⁻¹ᵁ V).toScheme :=
  (t₀).resLE (r ⁻¹ᵁ V) ((b₁) ⁻¹ᵁ V) (by
    rw [← Scheme.Hom.comp_preimage, labelTransition_first])

omit [Mono i] [Fintype J] in
/-- The first restricted closed endpoint is the original open coefficient map. -/
@[reassoc] theorem subframeDomainTransition_first :
    subframeDomainTransition (q := q) o o' ι i z r hr V ≫ (r ∣_ V) = (b₁) ∣_ V := by
  apply (cancel_mono V.ι).mp
  simp only [subframeDomainTransition, Category.assoc, morphismRestrict_ι,
    Scheme.Hom.resLE_comp_ι_assoc, labelTransition_first]

omit [Mono i] in
/-- The second restricted closed endpoint follows the full boundary subframe morphism. -/
@[reassoc] theorem subframeDomainTransition_second :
    subframeDomainTransition (q := q) o o' ι i z r hr V ≫ s.resLE V _ hV.le =
      subframeDomainMap e o o' ι i z r s hr hs V hV ≫ ((b₂) ∣_ V) := by
  apply (cancel_mono V.ι).mp
  simp only [subframeDomainTransition, subframeDomainMap, Category.assoc,
    Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, morphismRestrict_ι,
    subframeBoundaryMap_endpoint]

omit [Mono i] in
/-- Every original open closed-relation coefficient agrees after mixed-size subframe selection. -/
theorem subframeDomain_coefficient (t : Γ(V.toScheme, ⊤))
    (ht : (r ∣_ V).appTop t = (s.resLE V _ hV.le).appTop t) :
    (subframeDomainMap e o o' ι i z r s hr hs V hV).appTop (((b₂) ∣_ V).appTop t) =
      ((b₁) ∣_ V).appTop t := by
  change ((((b₂) ∣_ V).appTop ≫
    (subframeDomainMap e o o' ι i z r s hr hs V hV).appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, ← subframeDomainTransition_second]
  rw [Scheme.Hom.comp_appTop]
  change (subframeDomainTransition (q := q) o o' ι i z r hr V).appTop
    ((s.resLE V _ hV.le).appTop t) = _
  rw [← ht]
  change (((r ∣_ V).appTop ≫
    (subframeDomainTransition (q := q) o o' ι i z r hr V).appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, subframeDomainTransition_first]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
