/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.FiniteCoefficientUniverses

/-! # Flatness under coefficient extension in arbitrary universes

Open ideals in the target are handled using the original p-power models.
The tensor cancellation comparison retains the given representation.
-/

@[expose] public noncomputable section
open scoped TensorProduct NumberField
open IsDedekindDomain TensorProduct
namespace ThreeAdicPlan

set_option backward.isDefEq.respectTransparency false in
/-- Flatness survives a finite extension of coefficient rings. The explicit
topological hypotheses say that powers of `p` generate open ideals in `R`,
and every open ideal of `O` contains a power of `p` and has finite quotient.
These are satisfied by the adic coefficient rings in the normalization problem.
No flatness or surjectivity of `R → O` is required. -/
theorem flatAt_of_open_powers_universes
    (p : ℕ) {R O : Type*} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing O] [IsLocalRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Algebra R O] [ContinuousSMul R O]
    (hR : ∀ n : ℕ, IsOpen (Ideal.span {(p : R) ^ n} : Set R))
    (hO : ∀ J : Ideal O, IsOpen (J : Set O) →
      ∃ n : ℕ, (p : O) ^ n ∈ J ∧ Finite (O ⧸ J))
    {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (ρ : GaloisRep ℚ R V) (v : HeightOneSpectrum (𝓞 ℚ)) (hρ : ρ.IsFlatAt v) :
    (ρ.baseChange O).IsFlatAt v := by
  classical
  constructor
  intro J hJ
  obtain ⟨n, hn, hfin⟩ := hO J hJ
  let _ : Finite (O ⧸ J) := hfin
  let _ : ContinuousSMul R (O ⧸ J) := continuousSMul_of_algebraMap R (O ⧸ J) (by
    rw [IsScalarTower.algebraMap_eq R O (O ⧸ J), RingHom.coe_comp]
    exact (continuous_algebraMap O (O ⧸ J)).comp (continuous_algebraMap R O))
  let I : Ideal R := Ideal.span {(p : R) ^ n}
  have hI : I ≤ RingHom.ker (algebraMap R (O ⧸ J)) := by
    rw [Ideal.span_le]
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    change algebraMap R (O ⧸ J) ((p : R) ^ n) = 0
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hn :
      Ideal.Quotient.mk J ((p : O) ^ n) = 0)
  have hflat := finiteFlat_of_finite_coefficients_universes ρ v I hI (hρ.cond I (hR n))
  let σ₁ := (ρ.baseChange (O ⧸ J)).toLocal v
  let σ₂ := ((ρ.baseChange O).baseChange (O ⧸ J)).toLocal v
  let e : (O ⧸ J) ⊗[R] V ≃ₗ[R] (O ⧸ J) ⊗[O] (O ⊗[R] V) :=
    (AlgebraTensorModule.cancelBaseChange R O O (O ⧸ J) V).symm.restrictScalars R
  let t : σ₁.Space →+[Field.absoluteGaloisGroup (v.adicCompletion ℚ)] σ₂.Space :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro g x
        change e (σ₁ g x) = σ₂ g (e x)
        induction x using TensorProduct.inductionOn with
        | tmul a w =>
          simp only [σ₁, σ₂, GaloisRep.baseChange_map, GaloisRep.baseChange_tmul,
            e, LinearEquiv.restrictScalars_apply,
            AlgebraTensorModule.cancelBaseChange_symm_tmul]
        | add x y hx hy => simp_all }
  exact hflat.map _ _ _ _ t e.bijective


end ThreeAdicPlan
