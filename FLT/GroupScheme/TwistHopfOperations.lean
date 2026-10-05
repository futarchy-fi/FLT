/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GaloisIntegralCoordinates
public import FLT.GroupScheme.TwistTensorRecovery

/-!
# Descended Hopf operations on fixed twist coordinates

Equivariance restricts the original operations to invariants. The inverse of
the canonical tensor comparison gives comultiplication with its correct
integral target. Fixed scalar descent gives the counit in the original base.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent
universe u
variable {R S H : Type u} {G : Type*}
  [CommRing R] [CommRing S] [CommRing H] [Algebra R S] [HopfAlgebra R H] [Group G]
  (σ : G →* (S ≃ₐ[R] S)) (τ : G →* (H ≃ₐ[R] H))
  (hτ : ∀ g, ∃ f : H →ₐc[R] H, f.toAlgHom = (τ g).toAlgHom)

include hτ in
/-- Hopf-compatible coordinate actions commute with comultiplication. -/
theorem twistComul_equivariant (g : G) (x : H) :
    twistAction τ τ g (Bialgebra.comulAlgHom R H x) =
      Bialgebra.comulAlgHom R H (τ g x) := by
  obtain ⟨f, hf⟩ := hτ g
  have he := DFunLike.congr_fun (BialgHomClass.map_comp_comulAlgHom f) x
  change Algebra.TensorProduct.map f.toAlgHom f.toAlgHom _ =
    Bialgebra.comulAlgHom R H (f.toAlgHom x) at he
  rw [hf] at he
  exact he

include hτ in
/-- Hopf-compatible coordinate actions preserve the counit. -/
theorem twistCounit_invariant (g : G) (x : H) :
    Bialgebra.counitAlgHom R H (τ g x) = Bialgebra.counitAlgHom R H x := by
  obtain ⟨f, hf⟩ := hτ g
  have he := CoalgHomClass.counit_comp_apply f x
  change Bialgebra.counitAlgHom R H (f.toAlgHom x) = _ at he
  rw [hf] at he
  exact he

include hτ in
/-- Hopf-compatible coordinate actions commute with the antipode. -/
theorem twistAntipode_equivariant (g : G) (x : H) :
    τ g (HopfAlgebra.antipodeAlgHom R H x) = HopfAlgebra.antipodeAlgHom R H (τ g x) := by
  obtain ⟨f, hf⟩ := hτ g
  have he := LinearMap.congr_fun (BialgHom.antipode_comp f) x
  change HopfAlgebra.antipodeAlgHom R H (f.toAlgHom x) =
    f.toAlgHom (HopfAlgebra.antipodeAlgHom R H x) at he
  rw [hf] at he
  exact he.symm

/-- Antipode restricted to the actual invariant coordinate algebra. -/
def twistAntipode : twistModel σ τ →ₐ[R] twistModel σ τ :=
  twistMap σ τ τ (HopfAlgebra.antipodeAlgHom R H) (twistAntipode_equivariant τ hτ)

/-- Comultiplication obtained by inverting the canonical fixed tensor comparison. -/
def twistComul (ht : Function.Bijective (twistTensorMap σ τ τ)) :
    twistModel σ τ →ₐ[R] twistModel σ τ ⊗[R] twistModel σ τ :=
  (AlgEquiv.ofBijective (twistTensorMap σ τ τ) ht).symm.toAlgHom.comp
    (twistMap σ τ (twistAction τ τ) (Bialgebra.comulAlgHom R H)
      (twistComul_equivariant τ hτ))

/-- The descended comultiplication recovers the original one on invariant coordinates. -/
theorem twistTensorMap_comul (ht : Function.Bijective (twistTensorMap σ τ τ))
    (x : twistModel σ τ) :
    twistTensorMap σ τ τ (twistComul σ τ hτ ht x) =
      twistMap σ τ (twistAction τ τ) (Bialgebra.comulAlgHom R H)
        (twistComul_equivariant τ hτ) x :=
  (AlgEquiv.ofBijective (twistTensorMap σ τ τ) ht).apply_symm_apply _

/-- The counit on the scalar-extended ambient coordinates. -/
def scalarCounit : S ⊗[R] H →ₐ[R] S :=
  Algebra.TensorProduct.lift (AlgHom.id R S)
    ((Algebra.ofId R S).comp (Bialgebra.counitAlgHom R H)) (fun _ _ ↦ .all _ _)

include hτ in
/-- The scalar counit intertwines the semilinear action and the coefficient action. -/
theorem scalarCounit_equivariant (g : G) (z : S ⊗[R] H) :
    σ g (scalarCounit (R := R) (S := S) (H := H) z) =
      scalarCounit (twistAction σ τ g z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
    change σ g (s * algebraMap R S (Bialgebra.counitAlgHom R H x)) =
      σ g s * algebraMap R S (Bialgebra.counitAlgHom R H (τ g x))
    rw [map_mul, AlgEquiv.commutes, twistCounit_invariant τ hτ]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Counit descended all the way to the original coefficient ring. -/
def twistCounit (hinj : Function.Injective (algebraMap R S))
    (hfixed : ∀ s : S, (∀ g, σ g s = s) → ∃ r, algebraMap R S r = s) :
    twistModel σ τ →ₐ[R] R :=
  (fixedScalars σ hinj hfixed).symm.toAlgHom.comp
    (fixedMap (twistAction σ τ) σ scalarCounit (scalarCounit_equivariant σ τ hτ))

/-- The descended counit has the original scalar counit as its image. -/
theorem twistCounit_spec (hinj : Function.Injective (algebraMap R S))
    (hfixed : ∀ s : S, (∀ g, σ g s = s) → ∃ r, algebraMap R S r = s)
    (x : twistModel σ τ) :
    algebraMap R S (twistCounit σ τ hτ hinj hfixed x) = scalarCounit x.val :=
  congrArg Subtype.val ((fixedScalars σ hinj hfixed).apply_symm_apply _)

end SemilinearDescent
