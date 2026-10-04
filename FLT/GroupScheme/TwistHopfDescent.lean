/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.EtalePointHopf
public import FLT.GroupScheme.TwistHopfPoints
public import FLT.GroupScheme.HopfTorsor

/-!
# Hopf descent for the actual fixed twist algebra

Effective tensor descent constructs the operations. The original Hopf algebra's
convolution group and the complete generic point comparison verify every law.
Flatness and etaleness supply the separation argument over the integral base.
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

/-- The original Hopf antipode supplies convolution inverses on all closure-valued points. -/
local instance twistOriginalPointGroup : Group (WithConv (H →ₐ[R] Ω)) where
  inv f := WithConv.toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom R H))
  inv_mul_cancel f := HopfAlgebra.conv_antipode_mul f.ofConv

/-- The fixed integral coordinate algebra has the descended Hopf structure. -/
@[instance_reducible]
def twistHopf : HopfAlgebra R (twistModel σ τ) := fast_instance% (by
  let e : Additive (WithConv (H →ₐ[R] Ω)) → twistModel σ τ →ₐ[R] Ω :=
    fun f ↦ twistPoint σ τ s f.toMul.ofConv
  have he : Function.Surjective e := by
    intro f
    obtain ⟨g, hg⟩ := hp f
    exact ⟨Additive.ofMul (WithConv.toConv g), hg⟩
  refine PointCoalgebra.hopfOfEtalePoints (K := K) e he
    (twistComul σ τ hτ ht) (twistCounit σ τ hτ hinj hfixed) (twistAntipode σ τ hτ) ?_ ?_ ?_
  · intro x f g
    have hm : (f.toMul * g.toMul).ofConv =
        (Algebra.TensorProduct.lift f.toMul.ofConv g.toMul.ofConv
          (fun _ _ ↦ .all _ _)).comp (Bialgebra.comulAlgHom R H) := by
      ext z
      exact AlgHom.convMul_apply f.toMul g.toMul z
    change _ = twistPoint σ τ s (f.toMul * g.toMul).ofConv x
    rw [hm]
    exact DFunLike.congr_fun (twistPoint_comul σ τ hτ s ht f.toMul.ofConv g.toMul.ofConv) x
  · intro x
    exact DFunLike.congr_fun (twistPoint_counit σ τ hτ s hinj hfixed) x
  · intro x f
    exact DFunLike.congr_fun (twistPoint_antipode σ τ hτ s f.toMul.ofConv) x)

end SemilinearDescent
