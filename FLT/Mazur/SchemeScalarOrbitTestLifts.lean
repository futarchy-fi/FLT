/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarOrbitEndpoints
public import FLT.Mazur.ScalarOrbitTestLifts

/-!
# Scheme lifts of full original scalar coefficient tests

Equality on all invariant functions constructs a unique orbit-spectrum lift
of an arbitrary ring-valued tensor test. The coefficient ring is unchanged;
no reducedness, field, or scalar-fullness assumption is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SchemeScalarOrbitComparison
open SchemeCoordinateAction SchemeFiniteGroupQuotient FiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} [IsAffine X]
  (ρ : G →* Aut X) {R : Type u} [CommRing R]
  (s : R →+* invariantCoordinates ρ)
  (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ X) (g : G),
    a ≫ (ρ g).hom = a → g = 1)
  {B : Type u} [CommRing B] (t : tensorCoordinates ρ s →+* B)
/-- The original affine coefficient test with the tensor scheme kept sealed. -/
def tensorTest : Spec (.of B) ⟶ tensorScheme ρ s := by
  unfold tensorScheme
  exact Spec.map (CommRingCat.ofHom t)

include hfree

/-- Exact invariant endpoint agreement constructs the unique unchanged spectrum test lift. -/
theorem existsUnique_orbit_test_lift
    (ht : let _ := sourceAlgebra ρ s
      ∀ a : invariantCoordinates ρ,
        t (a.val ⊗ₜ[R] (1 : Γ(X, ⊤))) = t (1 ⊗ₜ[R] a.val)) :
    ∃! w : Spec (.of B) ⟶ Spec (.of (G → Γ(X, ⊤))),
      w ≫ orbitMap ρ s = tensorTest ρ s t := by
  unfold orbitMap tensorTest tensorScheme
  dsimp only [id]
  let _ := coordinateAction ρ
  let _ := s.toAlgebra
  let _ := sourceAlgebra ρ s
  let _ : IsScalarTower R (invariantCoordinates ρ) Γ(X, ⊤) :=
    IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨ψ, hψ, _⟩ :=
    (ScalarOrbitTensorComparison.existsUnique_lift_iff G R Γ(X, ⊤) t
      (coordinate_fixedPointIdeal_eq_top ρ hfree)).mpr ht
  let _ := orbitArrow_closedImmersion ρ s hfree
  refine ⟨Spec.map (CommRingCat.ofHom ψ), ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (coordinates ρ s)) = _
    rw [← Spec.map_comp]
    exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hψ
  · intro w hw
    apply (cancel_mono (orbitArrow ρ s)).mp
    rw [hw]
    change _ = Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (coordinates ρ s))
    rw [← Spec.map_comp]
    exact (congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hψ).symm

end FLT.Mazur.SchemeScalarOrbitComparison
