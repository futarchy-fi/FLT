/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineGeneratorPointCoefficientTransport
public import FLT.Mazur.SplitLineProjectiveFrame

/-!
# Dual projective transport of an arbitrary split vector

The coordinate principal covers of a vector and its transported vector
have affine intersections. Their actual normalized points satisfy the dual
transport law there, so the glued morphisms satisfy it on the entire source.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.SplitLinePrincipalPoints
open ProjectiveSpace FiniteFreeContragredient
variable {X : Scheme.{u}} [IsAffine X] {ι κ : Type u} [Finite ι] [Finite κ]
variable (e : (ι →₀ Γ(X, ⊤)) ≃ₗ[Γ(X, ⊤)] (κ →₀ Γ(X, ⊤)))
variable (v : ι → Γ(X, ⊤))

/-- Dual transport holds on every affine open with source and image unit coordinates. -/
lemma point_linearTransport (i : ι) (j : κ) (U : X.Opens) [IsAffine U.toScheme]
    (hi : U ≤ X.basicOpen (v i))
    (hj : U ≤ X.basicOpen (functionCoordinates e v j)) :
    point v i U hi ≫ (linearIso (map e)).hom =
      point (functionCoordinates e v) j U hj := by
  exact affineGeneratorPoint_linearTransport_coefficients U.ι.appTop.hom e v i j
    (coordinate_isUnit v i U hi).unit
    (coordinate_isUnit (functionCoordinates e v) j U hj).unit
    (coordinate_isUnit v i U hi).unit_spec.symm
    (coordinate_isUnit (functionCoordinates e v) j U hj).unit_spec.symm

omit [IsAffine X] in
/-- The original splitting canonically splits the transported vector. -/
lemma linearTransport_retraction
    (r : (ι → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤)) (hr : r v = 1) :
    (r.comp (functionCoordinates e).symm.toLinearMap) (functionCoordinates e v) = 1 := by
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using hr

/-- The actual glued point commutes with the genuine dual projective isomorphism. -/
lemma morphism_linearTransport
    (r : (ι → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤)) (hr : r v = 1)
    (q : (κ → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] Γ(X, ⊤))
    (hq : q (functionCoordinates e v) = 1) :
    morphism v r hr ≫ (linearIso (map e)).hom =
      morphism (functionCoordinates e v) q hq := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ i, X.basicOpen (v i) by rw [cover v r hr]; trivial)
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ j, X.basicOpen (functionCoordinates e v j) by
      rw [cover _ q hq]; trivial)
  let U := X.basicOpen (v i) ⊓ X.basicOpen (functionCoordinates e v j)
  let _ : IsAffine U.toScheme := by
    dsimp only [U]
    rw [← X.basicOpen_mul]
    infer_instance
  refine ⟨U, ⟨hi, hj⟩, ?_⟩
  rw [← Category.assoc, morphism_onOpen v r hr i U inf_le_left,
    morphism_onOpen _ q hq j U inf_le_right]
  exact point_linearTransport e v i j U inf_le_left inf_le_right

end FLT.Mazur.SplitLinePrincipalPoints
