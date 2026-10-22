/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarOrbitComparison

/-!
# Both original endpoints of the scalar orbit comparison

The tensor comparison has literal scheme endpoints. Its finite product
components are jointly epimorphic on arbitrary scheme targets, and its second
endpoint is the inverse action dictated by the coordinate convention.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
namespace FLT.Mazur.SchemeScalarOrbitComparison
open SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {G : Type u} [Group G] {X : Scheme.{u}} [IsAffine X]
  (ρ : G →* Aut X) {R : Type u} [CommRing R]
  (s : R →+* invariantCoordinates ρ)

/-- A sealed scheme model of the original scalar tensor product. -/
@[irreducible] def tensorScheme : Scheme.{u} := Spec (tensorCoordinates ρ s)

/-- The same orbit comparison with a sealed tensor target for geometric applications. -/
def orbitMap : Spec (.of (G → Γ(X, ⊤))) ⟶ tensorScheme ρ s := by
  unfold tensorScheme
  exact orbitArrow ρ s

/-- The first original scheme endpoint of the scalar tensor product. -/
def tensorFirst : tensorScheme ρ s ⟶ X := by
  unfold tensorScheme
  let _ := sourceAlgebra ρ s
  exact Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft
    (R := R) (S := R) (A := Γ(X, ⊤)) (B := Γ(X, ⊤))).toRingHom) ≫ X.isoSpec.inv

/-- The independent second endpoint of the same original scalar tensor product. -/
def tensorSecond : tensorScheme ρ s ⟶ X := by
  unfold tensorScheme
  let _ := sourceAlgebra ρ s
  exact Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫ X.isoSpec.inv

/-- The actual component of the finite orbit spectrum indexed by a group element. -/
def orbitComponent (g : G) : Spec Γ(X, ⊤) ⟶ Spec (.of (G → Γ(X, ⊤))) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ g))

omit [IsAffine X] [Group G] in
/-- Finite product components detect equality into every scheme, including nonaffine targets. -/
theorem orbitComponent_hom_ext [Finite G] {Y : Scheme.{u}}
    {a b : Spec (.of (G → Γ(X, ⊤))) ⟶ Y}
    (h : ∀ g, orbitComponent (X := X) g ≫ a = orbitComponent g ≫ b) : a = b := by
  apply (cancel_epi (sigmaSpec (fun _ : G ↦ Γ(X, ⊤)))).mp
  apply Sigma.hom_ext
  intro g
  simpa only [ι_sigmaSpec_assoc, orbitComponent] using h g

/-- The orbit comparison preserves its first endpoint on every full component. -/
@[reassoc] theorem orbitComponent_first (g : G) :
    orbitComponent g ≫ orbitMap ρ s ≫ tensorFirst ρ s = X.isoSpec.inv := by
  let _ := sourceAlgebra ρ s
  unfold orbitComponent orbitMap orbitArrow tensorFirst tensorScheme
  dsimp only [id]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  have h : CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := Γ(X, ⊤))
    (B := Γ(X, ⊤))).toRingHom ≫
      CommRingCat.ofHom (coordinates ρ s) ≫
        CommRingCat.ofHom (Pi.evalRingHom _ g) = 𝟙 Γ(X, ⊤) := by
    ext a
    change a * (ρ g⁻¹).hom.appTop 1 = a
    rw [map_one, mul_one]
  rw [h]
  exact (congrArg (fun f ↦ f ≫ X.isoSpec.inv) (Spec.map_id Γ(X, ⊤))).trans
    (Category.id_comp _)

/-- The independent second endpoint is the original inverse-action morphism. -/
@[reassoc] theorem orbitComponent_second (g : G) :
    orbitComponent g ≫ orbitMap ρ s ≫ tensorSecond ρ s =
      X.isoSpec.inv ≫ (ρ g⁻¹).hom := by
  let _ := sourceAlgebra ρ s
  unfold orbitComponent orbitMap orbitArrow tensorSecond tensorScheme
  dsimp only [id]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  have h : CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫
      CommRingCat.ofHom (coordinates ρ s) ≫
        CommRingCat.ofHom (Pi.evalRingHom _ g) = (ρ g⁻¹).hom.appTop := by
    ext a
    change 1 * (ρ g⁻¹).hom.appTop a = (ρ g⁻¹).hom.appTop a
    rw [one_mul]
  rw [h]
  exact Scheme.isoSpec_inv_naturality (ρ g⁻¹).hom

end FLT.Mazur.SchemeScalarOrbitComparison
