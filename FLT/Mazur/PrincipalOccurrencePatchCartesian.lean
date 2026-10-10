/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrencePatchRefinement

/-!
# Cartesian transition maps of occurrence patches

Refinement pulls back each patch image exactly. The universal property
of open immersions constructs its transition morphism, with composition
and a genuine cartesian square over the shared overlap.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

/-- An exact pullback of open images gives the range inclusion needed for a transition lift. -/
theorem openRange_comp_subset_of_preimage {U V X Y : Scheme}
    (i : U ⟶ X) (j : V ⟶ Y) (t : Y ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (h : t ⁻¹ᵁ i.opensRange = j.opensRange) : Set.range (j ≫ t) ⊆ Set.range i := by
  rintro _ ⟨z, rfl⟩
  change j z ∈ t ⁻¹ᵁ i.opensRange
  rw [h]
  exact ⟨z, rfl⟩

end FLT.Mazur

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalOccurrencePatchOpen
  FiniteRelationLocalization.transition

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}
  {x y : PrincipalOccurrenceStage dst a b f}


/-- The spectrum transition on a literal shared overlap. -/
abbrev principalOccurrenceOverlapTransition (hxy : x ≤ y) (j : κ) :
    Spec (.of (PrincipalStage R (B j) (b j) (y.target j))) ⟶
      Spec (.of (PrincipalStage R (B j) (b j) (x.target j))) :=
  Spec.map (CommRingCat.ofHom
    (principalTransition (b j) (principalOccurrence_target_mono hxy j)).toRingHom)

/-- The new patch maps into the old patch under the actual overlap transition. -/
def principalOccurrencePatchTransition (hxy : x ≤ y)
    (hx : ∀ i e, Function.Bijective (x.hom i e))
    (hy : ∀ i e, Function.Bijective (y.hom i e)) {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrencePatchScheme y p ⟶ principalOccurrencePatchScheme x p :=
  IsOpenImmersion.lift (principalOccurrencePatchOpen x hx p)
    (principalOccurrencePatchOpen y hy p ≫ principalOccurrenceOverlapTransition hxy j)
    (FLT.Mazur.openRange_comp_subset_of_preimage _ _ _
      (principalOccurrencePatch_preimage hxy hx hy p))

/-- The entire patch square commutes. -/
@[reassoc (attr := simp)] theorem principalOccurrencePatchTransition_fac (hxy : x ≤ y)
    (hx : ∀ i e, Function.Bijective (x.hom i e))
    (hy : ∀ i e, Function.Bijective (y.hom i e)) {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrencePatchTransition hxy hx hy p ≫ principalOccurrencePatchOpen x hx p =
      principalOccurrencePatchOpen y hy p ≫ principalOccurrenceOverlapTransition hxy j :=
  IsOpenImmersion.lift_fac _ _ _

/-- Patch transitions give genuine base-change squares. -/
theorem principalOccurrencePatchTransition_isPullback (hxy : x ≤ y)
    (hx : ∀ i e, Function.Bijective (x.hom i e))
    (hy : ∀ i e, Function.Bijective (y.hom i e)) {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    IsPullback (principalOccurrencePatchTransition hxy hx hy p)
      (principalOccurrencePatchOpen y hy p) (principalOccurrencePatchOpen x hx p)
      (principalOccurrenceOverlapTransition hxy j) := by
  apply IsOpenImmersion.isPullback
  · exact (principalOccurrencePatchTransition_fac hxy hx hy p).symm
  · exact principalOccurrencePatch_preimage hxy hx hy p

/-- Successive overlap transitions compose to the direct one. -/
theorem principalOccurrenceOverlapTransition_comp {z : PrincipalOccurrenceStage dst a b f}
    (hxy : x ≤ y) (hyz : y ≤ z) (j : κ) :
    principalOccurrenceOverlapTransition hyz j ≫ principalOccurrenceOverlapTransition hxy j =
      principalOccurrenceOverlapTransition (hxy.trans hyz) j := by
  simp only [principalOccurrenceOverlapTransition, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (principalTransition_comp (b j) _ _)

/-- Patch transitions compose on their full schemes. -/
theorem principalOccurrencePatchTransition_comp {z : PrincipalOccurrenceStage dst a b f}
    (hxy : x ≤ y) (hyz : y ≤ z)
    (hx : ∀ i e, Function.Bijective (x.hom i e))
    (hy : ∀ i e, Function.Bijective (y.hom i e))
    (hz : ∀ i e, Function.Bijective (z.hom i e)) {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrencePatchTransition hyz hy hz p ≫
      principalOccurrencePatchTransition hxy hx hy p =
        principalOccurrencePatchTransition (hxy.trans hyz) hx hz p := by
  rw [← cancel_mono (principalOccurrencePatchOpen x hx p)]
  simp only [Category.assoc, principalOccurrencePatchTransition_fac,
    principalOccurrencePatchTransition_fac_assoc, principalOccurrenceOverlapTransition_comp]

end FLT.Mazur.FiniteTypeRelationModel
