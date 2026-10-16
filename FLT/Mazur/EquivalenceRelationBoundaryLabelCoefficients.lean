/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryLabelChange

/-!
# Original open boundary coefficients across distinguished labels

Every function equalized by the entire original closed relation on its open
domain has identical pullbacks under exact boundary label transport. No extension
to a global original function and no reduced replacement of the boundary is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I] (o o' : I)
  (i : B ⟶ A) [Mono i] (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
  (V : B.Opens) (hV : r ⁻¹ᵁ V = s ⁻¹ᵁ V)
local notation "b₁" => endpoint (p := p) (q := q) I o i
local notation "b₂" => endpoint (p := p) (q := q) I o' i
local notation "t₀" => labelTransition (q := q) I o o' i z r hr
local notation "l" => labelMap e I o o' i z r s hr hs

include hV in
omit [Mono i] in
/-- The full original coefficient domain is preserved by exact closed label transport. -/
theorem labelMap_domain : (l) ⁻¹ᵁ ((b₂) ⁻¹ᵁ V) = (b₁) ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, labelMap_endpoint, Scheme.Hom.comp_preimage, ← hV,
    ← Scheme.Hom.comp_preimage, labelTransition_first]

/-- The label morphism restricted to the entire inverse image coefficient domain. -/
def labelDomainMap : ((b₁) ⁻¹ᵁ V).toScheme ⟶ ((b₂) ⁻¹ᵁ V).toScheme :=
  (l).resLE ((b₂) ⁻¹ᵁ V) ((b₁) ⁻¹ᵁ V) (labelMap_domain e I o o' i z r s hr hs V hV).ge

/-- The unchanged closed label arrow over the original section's open domain. -/
def labelDomainTransition : ((b₁) ⁻¹ᵁ V).toScheme ⟶ (r ⁻¹ᵁ V).toScheme :=
  (t₀).resLE (r ⁻¹ᵁ V) ((b₁) ⁻¹ᵁ V) (by
    rw [← Scheme.Hom.comp_preimage, labelTransition_first])

omit [Mono i] in
/-- The first restricted closed endpoint is the original open coefficient map. -/
@[reassoc] theorem labelDomainTransition_first :
    labelDomainTransition (q := q) I o o' i z r hr V ≫ (r ∣_ V) = (b₁) ∣_ V := by
  apply (cancel_mono V.ι).mp
  simp only [labelDomainTransition, Category.assoc, morphismRestrict_ι,
    Scheme.Hom.resLE_comp_ι_assoc, labelTransition_first]

omit [Mono i] in
/-- The second restricted closed endpoint follows the full boundary label morphism. -/
@[reassoc] theorem labelDomainTransition_second :
    labelDomainTransition (q := q) I o o' i z r hr V ≫ s.resLE V _ hV.le =
      labelDomainMap e I o o' i z r s hr hs V hV ≫ ((b₂) ∣_ V) := by
  apply (cancel_mono V.ι).mp
  simp only [labelDomainTransition, labelDomainMap, Category.assoc,
    Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, morphismRestrict_ι,
    labelMap_endpoint]

omit [Mono i] in
/-- Every original open closed-relation coefficient agrees after distinguished-label transport. -/
theorem labelDomain_coefficient (t : Γ(V.toScheme, ⊤))
    (ht : (r ∣_ V).appTop t = (s.resLE V _ hV.le).appTop t) :
    (labelDomainMap e I o o' i z r s hr hs V hV).appTop (((b₂) ∣_ V).appTop t) =
      ((b₁) ∣_ V).appTop t := by
  change ((((b₂) ∣_ V).appTop ≫
    (labelDomainMap e I o o' i z r s hr hs V hV).appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, ← labelDomainTransition_second]
  rw [Scheme.Hom.comp_appTop]
  change (labelDomainTransition (q := q) I o o' i z r hr V).appTop
    ((s.resLE V _ hV.le).appTop t) = _
  rw [← ht]
  change (((r ∣_ V).appTop ≫
    (labelDomainTransition (q := q) I o o' i z r hr V).appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, labelDomainTransition_first]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
