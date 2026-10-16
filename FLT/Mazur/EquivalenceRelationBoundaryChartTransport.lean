/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundarySubframeCoefficients

/-!
# Open boundary coefficients under independent chart restrictions

Subframe coefficient transport is valid on arbitrary open refinements of both
closed sources. Only the original section's invariant open domain is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J) (ι : J ↪ I)
  (i : B ⟶ A) (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
  (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
local notation "b₁" => endpoint (p := p) (q := q) I o i
local notation "b₂" => endpoint (p := p) (q := q) J o' i
local notation "l" => subframeBoundaryMap e o o' i z r s hr hs ι
variable (Q : (boundary (p := p) (q := q) I o i).Opens)
  (T : (boundary (p := p) (q := q) J o' i).Opens)
  (hQT : Q ≤ subframeBoundaryMap e o o' i z r s hr hs ι ⁻¹ᵁ T)
  (hT : T ≤ endpoint (p := p) (q := q) J o' i ⁻¹ᵁ E)

include hQT hT hE in
/-- Every chart refinement still lies over the full original coefficient domain. -/
theorem subframeChart_domain : Q ≤ (b₁) ⁻¹ᵁ E := by
  rw [← subframeBoundaryMap_domain e o o' ι i z r s hr hs E hE]
  exact hQT.trans ((l).preimage_mono hT)

/-- Arbitrary chart refinements preserve the actual original open boundary coefficient. -/
theorem subframeChart_coefficient (hQ : Q ≤ (b₁) ⁻¹ᵁ E) (t : Γ(E.toScheme, ⊤))
    (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t) :
    ((l).resLE T Q hQT).appTop (((b₂).resLE E T hT).appTop t) =
      ((b₁).resLE E Q hQ).appTop t := by
  let v := (labelTransition (q := q) I o (ι o') i z r hr).resLE (r ⁻¹ᵁ E) Q (by
    rw [← Scheme.Hom.comp_preimage, labelTransition_first]
    exact hQ)
  have hv₁ : v ≫ (r ∣_ E) = (b₁).resLE E Q hQ := by
    apply (cancel_mono E.ι).mp
    simp only [v, Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι_assoc, labelTransition_first]
  have hv₂ : v ≫ s.resLE E _ hE.le =
      (l).resLE T Q hQT ≫ (b₂).resLE E T hT := by
    apply (cancel_mono E.ι).mp
    simp only [v, Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.Hom.resLE_comp_ι_assoc, subframeBoundaryMap_endpoint]
  change ((((b₂).resLE E T hT).appTop ≫ ((l).resLE T Q hQT).appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, ← hv₂, Scheme.Hom.comp_appTop]
  change v.appTop ((s.resLE E _ hE.le).appTop t) = _
  rw [← ht]
  change (((r ∣_ E).appTop ≫ v.appTop) t) = _
  rw [← Scheme.Hom.comp_appTop, hv₁]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.InvariantBoundary
