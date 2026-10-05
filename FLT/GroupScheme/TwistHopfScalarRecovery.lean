/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.TwistHopfDescent
public import FLT.GroupScheme.BialgebraBaseChange

/-!
# Hopf-compatible scalar recovery

The canonical scalar recovery respects the descended counit and
comultiplication. It therefore recovers the original scalar-extended model
as a bialgebra, with antipode compatibility following for Hopf algebras.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace SemilinearDescent
variable {R S H : Type} [CommRing R] [CommRing S] [CommRing H]
  [Algebra R S] [HopfAlgebra R H]

/-- The ambient scalar counit is the counit of the scalar-extended Hopf algebra. -/
theorem scalarCounit_eq (z : S ⊗[R] H) :
    Coalgebra.counit (R := S) z = scalarCounit z := by
  induction z using TensorProduct.inductionOn with
  | tmul s h => simp [scalarCounit, TensorProduct.counit_tmul, Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Scalar tensor comparison identifies scalar-extended comultiplication. -/
theorem scalarTensorEquiv_comul (z : S ⊗[R] H) :
    scalarTensorEquiv R S H H (Coalgebra.comul (R := S) z) =
      Algebra.TensorProduct.map (AlgHom.id R S) (Bialgebra.comulAlgHom R H) z := by
  induction z using TensorProduct.inductionOn with
  | tmul s h =>
    simp only [TensorProduct.comul_tmul, CommSemiring.comul_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Bialgebra.comulAlgHom_apply]
    generalize Coalgebra.comul (R := R) h = w
    induction w using TensorProduct.inductionOn with
    | tmul x y => simp [scalarTensorEquiv_tmul]
    | add x y hx hy => simpa [TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy
  | add x y hx hy => simp only [map_add, hx, hy]

variable {K Ω : Type} {G : Type*} [Field K] [Field Ω]
  [Algebra R K] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
  [IsFractionRing R K] [IsGalois K Ω] [IsSepClosed Ω] [Group G]
  (σ : G →* (S ≃ₐ[R] S)) (τ : G →* (H ≃ₐ[R] H))
  (hτ : ∀ g, ∃ f : H →ₐc[R] H, f.toAlgHom = (τ g).toAlgHom)
  (ht : Function.Bijective (twistTensorMap σ τ τ))
  (hinj : Function.Injective (algebraMap R S))
  (hfixed : ∀ t : S, (∀ g, σ g t = t) → ∃ r, algebraMap R S r = t)
  (s : S →ₐ[R] Ω) (hp : Function.Surjective (twistPoint σ τ s))
  [Module.Flat R (twistModel σ τ)] [Algebra.Etale K (K ⊗[R] twistModel σ τ)]

/-- Effective scalar recovery is an equivalence of the constructed bialgebras. -/
def twistHopfRecovery
    (hr : Function.Bijective (recoveryMap (S := S) (twistAction σ τ))) :
    letI := twistHopf (K := K) σ τ hτ ht hinj hfixed s hp
    S ⊗[R] twistModel σ τ ≃ₐc[S] S ⊗[R] H := by
  letI := twistHopf (K := K) σ τ hτ ht hinj hfixed s hp
  apply ThreeAdicPlan.bialgebraScalarExtensionEquiv R S (twistModel σ τ) (S ⊗[R] H)
    (twistModel σ τ).val (twistRecoveryEquiv σ τ hr)
  · intro x
    simp [twistRecoveryEquiv_tmul]
  · intro x
    rw [scalarCounit_eq]
    exact twistCounit_spec σ τ hτ hinj hfixed x
  · intro x
    apply (scalarTensorEquiv R S H H).injective
    rw [scalarTensorEquiv_comul]
    have hh (z : twistModel σ τ ⊗[R] twistModel σ τ) :
        scalarTensorEquiv R S H H
          (ThreeAdicPlan.bialgebraScalarTensorMap R S (twistModel σ τ) (S ⊗[R] H)
            (twistModel σ τ).val z) = (twistTensorMap σ τ τ z).val := by
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        simpa [ThreeAdicPlan.bialgebraScalarTensorMap, twistTensorMap_tmul] using
          scalarTensorEquiv_product R S H H a.val b.val
      | add a b ha hb => simp only [map_add, ha, hb, Subalgebra.coe_add]
    rw [hh]
    exact congrArg Subtype.val (twistTensorMap_comul σ τ hτ ht x)

end SemilinearDescent
