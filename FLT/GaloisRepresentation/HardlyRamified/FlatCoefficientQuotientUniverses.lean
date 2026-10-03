/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs

/-! # Flatness through surjective coefficient maps in independent universes -/

@[expose] public noncomputable section
open scoped TensorProduct
open NumberField IsDedekindDomain TensorProduct
namespace ThreeAdicPlan

set_option backward.isDefEq.respectTransparency false in
/-- Flatness is preserved by a continuous quotient of coefficient rings.
For an open ideal `J` of the target, the first isomorphism theorem identifies
`R / preimage J` with `A / J`. The tensor-product equivalence identifies the
Galois modules, so the original finite flat model still works. -/
theorem flatAt_quotient_universes
    {R A : Type*} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra R A] [ContinuousSMul R A]
    (hsurj : Function.Surjective (algebraMap R A))
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (ρ : GaloisRep ℚ R V) (v : HeightOneSpectrum (𝓞 ℚ)) (hρ : ρ.IsFlatAt v) :
    (ρ.baseChange A).IsFlatAt v := by
  classical
  constructor
  intro J hJ
  let f : R →ₐ[R] A ⧸ J := Algebra.ofId R (A ⧸ J)
  let I : Ideal R := RingHom.ker f.toRingHom
  have hI : IsOpen (I : Set R) := by
    have hset : (I : Set R) = (algebraMap R A) ⁻¹' (J : Set A) := by
      ext x
      change algebraMap R (A ⧸ J) x = 0 ↔ algebraMap R A x ∈ J
      rw [IsScalarTower.algebraMap_apply R A (A ⧸ J)]
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [hset]
    exact hJ.preimage (continuous_algebraMap R A)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨r, rfl⟩ := hsurj a
    refine ⟨r, ?_⟩
    exact IsScalarTower.algebraMap_apply R A (A ⧸ J) r
  let ec : (R ⧸ I) ≃ₐ[R] (A ⧸ J) := Ideal.quotientKerAlgEquivOfSurjective hf
  let et : (R ⧸ I) ⊗[R] V ≃ₗ[R] (A ⧸ J) ⊗[A] (A ⊗[R] V) :=
    (TensorProduct.congr ec.toLinearEquiv (LinearEquiv.refl R V)).trans
      ((AlgebraTensorModule.cancelBaseChange R A A (A ⧸ J) V).symm.restrictScalars R)
  let σ₁ := (ρ.baseChange (R ⧸ I)).toLocal v
  let σ₂ := ((ρ.baseChange A).baseChange (A ⧸ J)).toLocal v
  let t : σ₁.Space →+[Field.absoluteGaloisGroup (v.adicCompletion ℚ)] σ₂.Space :=
    { et.toAddMonoidHom with
      map_smul' := by
        intro g x
        change et (σ₁ g x) = σ₂ g (et x)
        induction x using TensorProduct.inductionOn with
        | tmul a w =>
          simp only [σ₁, σ₂, GaloisRep.baseChange_map,
            GaloisRep.baseChange_tmul, et, LinearEquiv.trans_apply,
            TensorProduct.congr_tmul, LinearEquiv.refl_apply,
            LinearEquiv.restrictScalars_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul]
        | add x y hx hy => simp_all }
  exact (hρ.cond I hI).map _ _ _ _ t et.bijective

end ThreeAdicPlan
