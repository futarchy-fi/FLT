/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Ring.Compact

/-!
# Finite coefficient extensions preserve flatness

A finite coefficient quotient is an equivariant quotient of finitely many
copies of a reduction of the original representation. Finite products and
quotients of finite-flat Galois modules then supply the required model.
-/

@[expose] public section

open scoped TensorProduct NumberField
open IsDedekindDomain TensorProduct

namespace ThreeAdicPlan

set_option backward.isDefEq.respectTransparency false in
/-- A finite coefficient algebra annihilated by `I` gives a finite-flat
representation whenever reduction modulo `I` has a finite-flat model. -/
theorem finiteFlat_of_finite_coefficients
    {R S : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [Algebra R S] [ContinuousSMul R S] [Finite S]
    {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
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
  exact (hρ.finPow _ _ _ _ (Fintype.card S)).quotient _ _ _ _ q hq

set_option backward.isDefEq.respectTransparency false in
/-- Flatness survives a finite extension of coefficient rings. The explicit
topological hypotheses say that powers of `p` generate open ideals in `R`,
and every open ideal of `O` contains a power of `p` and has finite quotient.
These are satisfied by the adic coefficient rings in the normalization problem.
No flatness or surjectivity of `R → O` is required. -/
@[nolint unusedArguments]
theorem flatAt_of_open_powers
    (p : ℕ) {R O : Type} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing O] [IsLocalRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Algebra R O] [ContinuousSMul R O] [Module.Finite R O]
    (hR : ∀ n : ℕ, IsOpen (Ideal.span {(p : R) ^ n} : Set R))
    (hO : ∀ J : Ideal O, IsOpen (J : Set O) →
      ∃ n : ℕ, (p : O) ^ n ∈ J ∧ Finite (O ⧸ J))
    {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
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
  have hflat := finiteFlat_of_finite_coefficients ρ v I hI (hρ.cond I (hR n))
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

/-- Powers of `p` generate open ideals in a finite algebra over the p-adic
integers equipped with its module topology. No freeness is required. -/
@[nolint unusedArguments]
theorem isOpen_span_padic_pow
    {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] [IsModuleTopology ℤ_[p] R] (n : ℕ) :
    IsOpen (Ideal.span {(p : R) ^ n} : Set R) := by
  classical
  obtain ⟨d, f, hf⟩ := Module.Finite.exists_fin' ℤ_[p] R
  let P : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p]) ^ n}
  have hP : IsOpen (P : Set ℤ_[p]) := by
    apply IsDedekindDomain.isOpen_of_ne_bot
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hopen : IsOpen {x : Fin d → ℤ_[p] | ∀ i, x i ∈ P} := by
    simpa [Set.pi] using
      (isOpen_set_pi Set.finite_univ (fun _ _ ↦ hP) :
        IsOpen (Set.univ.pi fun _ : Fin d ↦ (P : Set ℤ_[p])))
  have himage : f '' {x : Fin d → ℤ_[p] | ∀ i, x i ∈ P} =
      (Ideal.span {(p : R) ^ n} : Set R) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      choose a ha using fun i ↦ Ideal.mem_span_singleton.mp (hx i)
      have hx' : x = (p : ℤ_[p]) ^ n • a := by
        funext i
        exact ha i
      rw [hx', map_smul]
      rw [Algebra.smul_def, map_pow, map_natCast]
      exact Ideal.mem_span_singleton.mpr ⟨f a, rfl⟩
    · intro hy
      obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
      obtain ⟨b, rfl⟩ := hf a
      refine ⟨(p : ℤ_[p]) ^ n • b, ?_, ?_⟩
      · intro i
        exact Ideal.mem_span_singleton.mpr ⟨b i, rfl⟩
      · rw [map_smul, Algebra.smul_def, map_pow, map_natCast]
        exact ha.symm
  rw [← himage]
  exact IsModuleTopology.isOpenMap_of_surjective hf _ hopen

/-- The generic normalization-flatness input: any module-finite continuous
extension of a finite p-adic coefficient algebra preserves flatness, provided
its open ideals contain powers of `p` and have finite quotients. In particular,
this applies to a DVR normalization with its adic topology. -/
@[nolint unusedArguments]
theorem flat_three_normalization
    {p : ℕ} [Fact p.Prime] {R O : Type} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] [IsModuleTopology ℤ_[p] R]
    [CommRing O] [IsLocalRing O] [TopologicalSpace O] [IsTopologicalRing O]
    [Algebra R O] [ContinuousSMul R O] [Module.Finite R O]
    (hO : ∀ J : Ideal O, IsOpen (J : Set O) →
      ∃ n : ℕ, (p : O) ^ n ∈ J ∧ Finite (O ⧸ J))
    {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (ρ : GaloisRep ℚ R V) (v : HeightOneSpectrum (𝓞 ℚ)) (hρ : ρ.IsFlatAt v) :
    (ρ.baseChange O).IsFlatAt v :=
  flatAt_of_open_powers p (fun n ↦ isOpen_span_padic_pow n) hO ρ v hρ

end ThreeAdicPlan
