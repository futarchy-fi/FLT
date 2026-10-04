/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.TwistHopfOperations
public import FLT.GroupScheme.TwistPointTensor

/-!
# Group operations on points of the descended coordinates

The descended comultiplication, counit and antipode evaluate as the original
point product, identity and inverse. These formulas use the constructed
operations, not an assumed Hopf structure on the fixed algebra.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent
universe u
variable {R S H Ω : Type u} {G : Type*}
  [CommRing R] [CommRing S] [CommRing H] [CommRing Ω]
  [Algebra R S] [HopfAlgebra R H] [Algebra R Ω] [Group G]
  (σ : G →* (S ≃ₐ[R] S)) (τ : G →* (H ≃ₐ[R] H))
  (hτ : ∀ g, ∃ f : H →ₐc[R] H, f.toAlgHom = (τ g).toAlgHom)
  (s : S →ₐ[R] Ω)

/-- The descended comultiplication evaluates as the original convolution product. -/
theorem twistPoint_comul (ht : Function.Bijective (twistTensorMap σ τ τ))
    (f g : H →ₐ[R] Ω) :
    (Algebra.TensorProduct.lift (twistPoint σ τ s f) (twistPoint σ τ s g)
      (fun _ _ ↦ .all _ _)).comp (twistComul σ τ hτ ht) =
      twistPoint σ τ s ((Algebra.TensorProduct.lift f g (fun _ _ ↦ .all _ _)).comp
        (Bialgebra.comulAlgHom R H)) := by
  rw [← twistPoint_tensor]
  rw [AlgHom.comp_assoc]
  have hc : (twistTensorMap σ τ τ).comp (twistComul σ τ hτ ht) =
      twistMap σ τ (twistAction τ τ) (Bialgebra.comulAlgHom R H)
        (twistComul_equivariant τ hτ) := by
    apply AlgHom.ext
    intro x
    exact twistTensorMap_comul σ τ hτ ht x
  rw [hc, twistPoint_map]

/-- The descended antipode evaluates as the original inverse. -/
theorem twistPoint_antipode (f : H →ₐ[R] Ω) :
    (twistPoint σ τ s f).comp (twistAntipode σ τ hτ) =
      twistPoint σ τ s (f.comp (HopfAlgebra.antipodeAlgHom R H)) :=
  twistPoint_map σ τ τ s f _ _

/-- Coefficient evaluation intertwines the original scalar counit. -/
theorem scalarCounit_evaluate (z : S ⊗[R] H) :
    s (scalarCounit z) = Algebra.TensorProduct.lift s
      ((Algebra.ofId R Ω).comp (Bialgebra.counitAlgHom R H)) (fun _ _ ↦ .all _ _) z := by
  induction z using TensorProduct.inductionOn with
  | tmul t h =>
    change s (t * algebraMap R S (Bialgebra.counitAlgHom R H h)) =
      s t * algebraMap R Ω (Bialgebra.counitAlgHom R H h)
    rw [map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The descended counit evaluates as the original identity point. -/
theorem twistPoint_counit (hinj : Function.Injective (algebraMap R S))
    (hfixed : ∀ t : S, (∀ g, σ g t = t) → ∃ r, algebraMap R S r = t) :
    (Algebra.ofId R Ω).comp (twistCounit σ τ hτ hinj hfixed) =
      twistPoint σ τ s ((Algebra.ofId R Ω).comp (Bialgebra.counitAlgHom R H)) := by
  ext x
  change algebraMap R Ω (twistCounit σ τ hτ hinj hfixed x) = _
  rw [← s.commutes, twistCounit_spec]
  exact scalarCounit_evaluate s x.val

end SemilinearDescent
