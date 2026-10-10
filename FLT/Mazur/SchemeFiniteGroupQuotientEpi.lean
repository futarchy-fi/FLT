/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupAffineDescent
public import FLT.Mazur.SchemeFiniteGroupInvariantPrincipal
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Epimorphisms from affine finite-group quotients

Affine-target uniqueness extends to arbitrary targets by restricting both
morphisms to a common affine target neighborhood and an invariant principal
source neighborhood. This proves equality of scheme morphisms, including
structure-sheaf maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] {X : Scheme.{u}} [IsAffine X]
variable (ρ : G →* Aut X)

/-- Affine-target cancellation is the invariant-coordinate universal property. -/
lemma quotientMap_cancel_affine {Y : Scheme.{u}} [IsAffine Y]
    (a b : quotient ρ ⟶ Y) (h : quotientMap ρ ≫ a = quotientMap ρ ≫ b) : a = b := by
  obtain ⟨k, _, hk⟩ := existsUnique_affine_desc ρ (quotientMap ρ ≫ a)
    (fun g ↦ by rw [quotientMap_invariant_assoc])
  exact (hk a rfl).trans (hk b h.symm).symm

omit [IsAffine X] in
/-- Naturality for the actual invariant principal chart. -/
@[reassoc]
lemma principalQuotientMap_fac (r : invariantCoordinates ρ) :
    quotientMap (principalAction ρ r) ≫ principalQuotientMap ρ r =
      (X.basicOpen (r : Γ(X, ⊤))).ι ≫ quotientMap ρ :=
  quotientMap_naturality _ _ _ _

variable [Finite G]

/-- Cancellation through an affine finite-group quotient holds for every scheme target. -/
lemma quotientMap_cancel {Y : Scheme.{u}} (a b : quotient ρ ⟶ Y)
    (h : quotientMap ρ ≫ a = quotientMap ρ ≫ b) : a = b := by
  apply Scheme.hom_ext_of_forall
  intro z
  have hab (w : quotient ρ) : a w = b w := by
    obtain ⟨x, rfl⟩ := (quotientMap ρ).surjective w
    exact congrArg (fun k : X ⟶ Y ↦ k x) h
  obtain ⟨V, hV, hzV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show a z ∈ (⊤ : Y.Opens) from trivial)
  let _ : IsAffine V.toScheme := hV
  have hz : z ∈ a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V := ⟨hzV, by change b z ∈ V; rw [← hab]; exact hzV⟩
  obtain ⟨_, ⟨r, rfl⟩, hzr, hr⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := invariantCoordinates ρ)).isOpen_iff.mp
      (a ⁻¹ᵁ V ⊓ b ⁻¹ᵁ V).isOpen z hz
  let j := principalQuotientMap ρ r
  have hj (w : quotient (principalAction ρ r)) : j w ∈ PrimeSpectrum.basicOpen r := by
    rw [← principalQuotientMap_opensRange ρ r]
    exact ⟨w, rfl⟩
  have ha : Set.range (j ≫ a) ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hr (hj w)).1
  have hb : Set.range (j ≫ b) ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hr (hj w)).2
  let a' := IsOpenImmersion.lift V.ι (j ≫ a) ha
  let b' := IsOpenImmersion.lift V.ι (j ≫ b) hb
  have he : a' = b' := by
    apply quotientMap_cancel_affine (principalAction ρ r)
    rw [← cancel_mono V.ι]
    simp only [Category.assoc, a', b', IsOpenImmersion.lift_fac]
    change quotientMap (principalAction ρ r) ≫ principalQuotientMap ρ r ≫ a =
      quotientMap (principalAction ρ r) ≫ principalQuotientMap ρ r ≫ b
    rw [principalQuotientMap_fac_assoc, principalQuotientMap_fac_assoc, h]
  have hjab : j ≫ a = j ≫ b := by
    rw [← IsOpenImmersion.lift_fac V.ι (j ≫ a) ha,
      ← IsOpenImmersion.lift_fac V.ι (j ≫ b) hb]
    exact congrArg (fun k ↦ k ≫ V.ι) he
  let U : (quotient ρ).Opens := PrimeSpectrum.basicOpen r
  have hrange : Set.range j = Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact congrArg (fun W : (quotient ρ).Opens ↦ (W : Set (quotient ρ)))
      (principalQuotientMap_opensRange ρ r)
  let e := IsOpenImmersion.isoOfRangeEq j U.ι hrange
  refine ⟨U, hzr, ?_⟩
  rw [← cancel_epi e.hom, ← Category.assoc, ← Category.assoc]
  rw [show e.hom ≫ U.ι = j from IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _]
  exact hjab

/-- The affine quotient morphism is an epimorphism in the category of schemes. -/
instance quotientMap_epi : Epi (quotientMap ρ) :=
  ⟨fun a b h ↦ quotientMap_cancel ρ a b h⟩

end FLT.Mazur.SchemeFiniteGroupQuotient
