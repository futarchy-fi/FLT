/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.TwistHopfDescent
public import FLT.GroupScheme.EtalePointCocommutativity

/-!
# Convolution comparison and cocommutativity of the descended Hopf algebra

The algebra-point comparison preserves convolution for the constructed Hopf
structure. A cocommutative original algebra gives a cocommutative integral twist.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent
universe u
variable {R S K H Ω : Type u} {G : Type*}
  [CommRing R] [CommRing S] [Field K] [CommRing H] [Field Ω]
  [Algebra R S] [HopfAlgebra R H] [Algebra R K] [Algebra R Ω] [Algebra K Ω]
  [IsScalarTower R K Ω] [IsFractionRing R K] [IsGalois K Ω] [IsSepClosed Ω] [Group G]
  (σ : G →* (S ≃ₐ[R] S)) (τ : G →* (H ≃ₐ[R] H))
  (hτ : ∀ g, ∃ f : H →ₐc[R] H, f.toAlgHom = (τ g).toAlgHom)
  (ht : Function.Bijective (twistTensorMap σ τ τ))
  (hinj : Function.Injective (algebraMap R S))
  (hfixed : ∀ t : S, (∀ g, σ g t = t) → ∃ r, algebraMap R S r = t)
  (s : S →ₐ[R] Ω) (hp : Function.Surjective (twistPoint σ τ s))
  [Module.Flat R (twistModel σ τ)] [Algebra.Etale K (K ⊗[R] twistModel σ τ)]

/-- The original and descended geometric algebra points have the same convolution law. -/
theorem twistPoint_convMul (f g : WithConv (H →ₐ[R] Ω)) :
    letI := twistHopf (K := K) σ τ hτ ht hinj hfixed s hp
    WithConv.toConv (twistPoint σ τ s (f * g).ofConv) =
      WithConv.toConv (twistPoint σ τ s f.ofConv) *
        WithConv.toConv (twistPoint σ τ s g.ofConv) := by
  let := twistHopf (K := K) σ τ hτ ht hinj hfixed s hp
  apply WithConv.ofConv_injective
  ext x
  rw [AlgHom.convMul_apply]
  have hm : (f * g).ofConv =
      (Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ ↦ .all _ _)).comp
        (Bialgebra.comulAlgHom R H) := by
    ext z
    exact AlgHom.convMul_apply f g z
  rw [hm]
  exact (DFunLike.congr_fun (twistPoint_comul σ τ hτ s ht f.ofConv g.ofConv) x).symm

/-- Effective point recovery is an isomorphism of the actual convolution groups. -/
def twistPointMulEquiv (hi : Function.Injective (twistPoint σ τ s)) :
    letI := twistHopf (K := K) σ τ hτ ht hinj hfixed s hp
    WithConv (H →ₐ[R] Ω) ≃* WithConv (twistModel σ τ →ₐ[R] Ω) := by
  letI := twistHopf (K := K) σ τ hτ ht hinj hfixed s hp
  exact {
  toEquiv := Equiv.ofBijective (fun f ↦ WithConv.toConv (twistPoint σ τ s f.ofConv))
    ⟨fun _ _ h ↦ WithConv.ofConv_injective (hi (congrArg WithConv.ofConv h)),
      fun f ↦ by
        obtain ⟨g, hg⟩ := hp f.ofConv
        exact ⟨WithConv.toConv g, congrArg WithConv.toConv hg⟩⟩
  map_mul' := twistPoint_convMul (K := K) σ τ hτ ht hinj hfixed s hp }

/-- Cocommutativity makes convolution on the original points a commutative group. -/
local instance originalPointCommGroup [Coalgebra.IsCocomm R H] :
    CommGroup (WithConv (H →ₐ[R] Ω)) where
  inv f := WithConv.toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R H))
  inv_mul_cancel f := HopfAlgebra.conv_antipode_mul f.ofConv
  mul_comm := mul_comm

/-- Cocommutativity descends to the actual fixed Hopf algebra. -/
theorem twistIsCocomm [Coalgebra.IsCocomm R H] :
    let := twistHopf (K := K) σ τ hτ ht hinj hfixed s hp
    Coalgebra.IsCocomm R (twistModel σ τ) := by
  let := twistHopf (K := K) σ τ hτ ht hinj hfixed s hp
  let e : Additive (WithConv (H →ₐ[R] Ω)) → twistModel σ τ →ₐ[R] Ω :=
    fun f ↦ twistPoint σ τ s f.toMul.ofConv
  have he : Function.Surjective e := by
    intro f
    obtain ⟨g, hg⟩ := hp f
    exact ⟨Additive.ofMul (WithConv.toConv g), hg⟩
  apply PointCoalgebra.isCocomm_of_points (K := K) e he
  intro x f g
  have hm := congrArg (fun q ↦ q x)
    (congrArg WithConv.ofConv
      (twistPoint_convMul (K := K) σ τ hτ ht hinj hfixed s hp f.toMul g.toMul))
  rw [AlgHom.convMul_apply] at hm
  exact hm.symm

end SemilinearDescent
