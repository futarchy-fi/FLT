/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.GroupScheme.FiniteFlatQuotientUniverses

/-! # Finite coefficient extension in arbitrary universes

The original coefficient and module universes are retained. Only the finite
point quotient construction uses the proved universe-transport lemma.
-/

@[expose] public noncomputable section
open scoped TensorProduct NumberField
open IsDedekindDomain TensorProduct
namespace ThreeAdicPlan

set_option backward.isDefEq.respectTransparency false in
/-- A finite coefficient algebra annihilated by `I` gives a finite-flat
representation whenever reduction modulo `I` has a finite-flat model. -/
theorem finiteFlat_of_finite_coefficients_universes
    {R S : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra R S] [ContinuousSMul R S] [Finite S]
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (ρ : GaloisRep ℚ R V) (v : HeightOneSpectrum (𝓞 ℚ)) (I : Ideal R)
    (hI : I ≤ RingHom.ker (algebraMap R S))
    (hρ : (ρ.baseChange (R ⧸ I)).HasFlatProlongationAt v) :
    (ρ.baseChange S).HasFlatProlongationAt v := by
  classical
  let _ : Fintype S := Fintype.ofFinite S
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  let f : (R ⧸ I) →ₐ[R] S := Ideal.Quotient.liftₐ I (Algebra.ofId R S) (fun _ hx ↦ hI hx)
  let σ₁ := (ρ.baseChange (R ⧸ I)).toLocal v
  let σ₂ := (ρ.baseChange S).toLocal v
  let t : (R ⧸ I) ⊗[R] V →ₗ[R] S ⊗[R] V :=
    TensorProduct.map f.toLinearMap (LinearMap.id : V →ₗ[R] V)
  let q₀ (a : S) : σ₁.Space →+[Field.absoluteGaloisGroup (v.adicCompletion ℚ)]
      σ₂.Space :=
    { (a • t).toAddMonoidHom with
      map_smul' := by
        intro g x
        change a • t (σ₁ g x) = σ₂ g (a • t x)
        rw [map_smul]
        congr 1
        induction x using TensorProduct.inductionOn with
        | tmul r w => rfl
        | add x y hx hy => simp_all }
  let q : (Fin (Fintype.card S) → σ₁.Space)
      →+[Field.absoluteGaloisGroup (v.adicCompletion ℚ)] σ₂.Space :=
    { toFun := fun x ↦ ∑ i, q₀ (e i) (x i)
      map_zero' := by simp
      map_add' := by intro x y; simp [Finset.sum_add_distrib]
      map_smul' := by intro g x; simp [Finset.smul_sum] }
  have hq : Function.Surjective q := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a w =>
        refine ⟨Pi.single (e.symm a) (1 ⊗ₜ[R] w), ?_⟩
        change (∑ i, q₀ (e i) ((Pi.single (e.symm a) ((1 : R ⧸ I) ⊗ₜ[R] w) :
          Fin (Fintype.card S) → σ₁.Space) i)) = _
        rw [Finset.sum_eq_single (e.symm a)]
        · rw [Pi.single_eq_same]
          change e (e.symm a) • t (1 ⊗ₜ[R] w) = _
          simp [t, TensorProduct.smul_tmul']
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb]
        · simp
    | add x y hx hy =>
        obtain ⟨x, rfl⟩ := hx
        obtain ⟨y, rfl⟩ := hy
        exact ⟨x + y, map_add q x y⟩
  exact (hρ.finPow _ _ _ _ (Fintype.card S)).quotient_universes _ _ _ _ q hq


end ThreeAdicPlan
