/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRepFamily
public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# General inputs for B5

The general input `not_isIrreducible_of_frobenius_traces` (Chebotarev and
Brauer--Nesbitt) remains admitted. Neither it nor the domain-quotient construction
uses the hardly-ramified hypothesis or any B6 theorem.
Coefficient-quotient preservation, trace/base-change identities, injectivity
of coefficient embeddings, and compatibility transport are proved below.
-/

@[expose] public section

open scoped TensorProduct NumberField
open IsDedekindDomain TensorProduct

namespace GaloisRepresentation.B5Inputs

/-- A finite free local algebra over `ℤ_[p]` has a characteristic-zero domain
quotient through which a given map to a field factors. Choose a minimal prime
contained in the kernel of that map. Flatness over the DVR ensures the prime
avoids `p`. The quotient is local and finite torsion-free, hence free over the
DVR. Give it the quotient (equivalently module) topology.

This is a commutative-algebra input, with no representation-theoretic hypothesis. -/
theorem exists_domain_quotient {p : ℕ} [Fact p.Prime]
    (R : Type) [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    [IsModuleTopology ℤ_[p] R]
    (k : Type) [Field k] [Algebra R k] :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A)
      (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : Algebra ℤ_[p] A) (_ : Module.Finite ℤ_[p] A) (_ : Module.Free ℤ_[p] A)
      (_ : IsModuleTopology ℤ_[p] A)
      (_ : Algebra R A) (_ : IsScalarTower ℤ_[p] R A) (_ : ContinuousSMul R A)
      (_ : Algebra A k) (_ : IsScalarTower R A k),
      Function.Surjective (algebraMap R A) := by
  classical
  let : (RingHom.ker (algebraMap R k)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPk⟩ := Ideal.exists_minimalPrimes_le
    (show (⊥ : Ideal R) ≤ RingHom.ker (algebraMap R k) from bot_le)
  let : P.IsPrime := hP.isPrime
  let A := R ⧸ P
  let : IsLocalRing A :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hinj : Function.Injective (algebraMap ℤ_[p] A) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    by_contra hne
    have hxP : algebraMap ℤ_[p] R x ∈ P := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact hx
    apply notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hxP hP
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have hxy : x • y = 0 := by simpa [Algebra.smul_def, mul_comm] using hy
    exact (smul_eq_zero.mp hxy).resolve_left hne
  let : Module.IsTorsionFree ℤ_[p] A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  let : TopologicalSpace A := moduleTopology ℤ_[p] A
  let : IsModuleTopology ℤ_[p] A := ⟨rfl⟩
  let : IsTopologicalRing A := IsModuleTopology.isTopologicalRing ℤ_[p] A
  let : ContinuousSMul R A := continuousSMul_of_algebraMap R A
    (IsModuleTopology.continuous_of_linearMap
      (IsScalarTower.toAlgHom ℤ_[p] R A).toLinearMap)
  let f : A →+* k := Ideal.Quotient.lift P (algebraMap R k) hPk
  let : Algebra A k := f.toAlgebra
  let : IsScalarTower R A k := IsScalarTower.of_algebraMap_eq' rfl
  exact ⟨A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Ideal.Quotient.mk_surjective⟩

set_option backward.isDefEq.respectTransparency false in
/-- Flatness is preserved by a continuous quotient of coefficient rings.
For an open ideal `J` of the target, the first isomorphism theorem identifies
`R / preimage J` with `A / J`. The tensor-product equivalence identifies the
Galois modules, so the original finite flat model still works. -/
theorem flatAt_quotient
    {R A : Type} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra R A] [ContinuousSMul R A]
    (hsurj : Function.Surjective (algebraMap R A))
    {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
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

set_option backward.isDefEq.respectTransparency false in
/-- Coefficient quotients preserve hardly ramified representations. Flatness
follows by identifying the reductions modulo open ideals. The rank-one quotient
at 2 remains surjective after tensoring; its character remains unramified and
has square one. -/
theorem hardlyRamified_quotient {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    {R A : Type} [CommRing R] [IsLocalRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R] [IsModuleTopology ℤ_[p] R]
    [CommRing A] [IsLocalRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra ℤ_[p] A] [Module.Finite ℤ_[p] A] [Module.Free ℤ_[p] A]
    [IsModuleTopology ℤ_[p] A] [Algebra R A] [IsScalarTower ℤ_[p] R A]
    [ContinuousSMul R A] (hsurj : Function.Surjective (algebraMap R A))
    {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) (hVA : Module.rank A (A ⊗[R] V) = 2)
    {ρ : GaloisRep ℚ R V} (hρ : IsHardlyRamified hpodd hV ρ) :
    IsHardlyRamified hpodd hVA (ρ.baseChange A) := by
  refine ⟨?_, ?_, flatAt_quotient hsurj ρ _ hρ.isFlat, ?_⟩
  · intro g
    change ((ρ g).baseChange A).det = _
    rw [LinearMap.det_baseChange]
    change algebraMap R A (ρ.det g) = _
    rw [hρ.det, ← IsScalarTower.algebraMap_apply ℤ_[p] R A]
  · intro q hq hgood
    have := hρ.isUnramified q hq hgood
    infer_instance
  · obtain ⟨π, hπ, δ, hδ⟩ := hρ.isTameAtTwo
    let e : A ⊗[R] R ≃ₗ[A] A := AlgebraTensorModule.rid R A A
    let πA : A ⊗[R] V →ₗ[A] A := e.toLinearMap.comp (π.baseChange A)
    let δA := (δ.baseChange A).conj e
    have hker : δ.ker ≤ δA.ker := by
      dsimp [δA]
      rw [GaloisRep.ker_conj]
      exact δ.ker_baseChange
    refine ⟨πA, e.surjective.comp (π.baseChange_surjective A hπ), δA, ?_⟩
    intro g x
    refine ⟨?_, (hδ 1 0).2.1.trans hker, ?_⟩
    · induction x using TensorProduct.inductionOn with
      | tmul a v =>
        have hv := (hδ g v).1
        have hδlin : δ g (π v) = π v • δ g 1 := by
          simpa using (δ g).map_smul (π v) (1 : R)
        simp only [GaloisRep.baseChange_map, GaloisRep.baseChange_tmul,
          πA, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
          e, AlgebraTensorModule.rid_tmul, δA, GaloisRep.conj_apply_apply,
          AlgebraTensorModule.rid_symm_apply]
        rw [hv, hδlin]
        simp [smul_smul, mul_comm]
      | add x y hx hy => simp_all
    · intro g
      have hgg : g * g ∈ δ.ker := by
        change δ (g * g) = 1
        rw [map_mul, (hδ 1 0).2.2 g]
      have hggA := hker hgg
      change δA (g * g) = 1 at hggA
      rwa [map_mul] at hggA

/-- Chebotarev and Brauer--Nesbitt, in the rank-two finite-field form needed here.
A continuous representation with cyclotomic determinant and Frobenius traces
`1 + q` outside finitely many places has semisimplification `1 ⊕ cyclotomic`,
and so cannot be irreducible. Chebotarev identifies characteristic polynomials
on the finite image; Brauer--Nesbitt identifies the semisimplifications. The
exceptional set may include the ramified places. This statement imposes no
flatness or hardly-ramified condition.

The characteristic bound avoids small-characteristic trace-only issues; trace
and determinant together determine the characteristic polynomial in rank two. -/
theorem not_isIrreducible_of_frobenius_traces
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {k : Type} [Field k] [Finite k] [TopologicalSpace k] [DiscreteTopology k]
    [Algebra ℤ_[p] k] [IsLocalHom (algebraMap ℤ_[p] k)]
    {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) (ρ : GaloisRep ℚ k V)
    (hdet : ∀ g, ρ.det g = algebraMap ℤ_[p] k
      (cyclotomicCharacter (AlgebraicClosure ℚ) p g.toRingEquiv))
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (htrace : ∀ q (hq : Nat.Prime q), 5 ≤ q → q ≠ p →
      hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
      (ρ.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
        (Field.AbsoluteGaloisGroup.adicArithFrob
          hq.toHeightOneSpectrumRingOfIntegersRat)).trace k V = 1 + q) :
    ¬ ρ.IsIrreducible := by
  sorry

/-- Traces commute with coefficient extension and change of basis. -/
theorem trace_baseChange_conj {K R A V W : Type*} [Field K] [CommRing R] [CommRing A]
    [TopologicalSpace R] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra R A] [ContinuousSMul R A]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [AddCommGroup W] [Module A W]
    (ρ : GaloisRep K R V) (e : A ⊗[R] V ≃ₗ[A] W)
    (g : Field.absoluteGaloisGroup K) :
    (((ρ.baseChange A).conj e) g).trace A W = algebraMap R A ((ρ g).trace R V) := by
  change (e.conj ((ρ g).baseChange A)).trace A W = _
  rw [LinearMap.trace_conj', LinearMap.trace_baseChange]

/-- The trace identity for the chosen local Frobenius, avoiding any change in
the chosen embedding of algebraic closures used to restrict a representation. -/
theorem trace_toLocal_baseChange_conj {R A V W : Type*} [CommRing R] [CommRing A]
    [TopologicalSpace R] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra R A] [ContinuousSMul R A]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    [AddCommGroup W] [Module A W]
    (ρ : GaloisRep ℚ R V) (e : A ⊗[R] V ≃ₗ[A] W)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((((ρ.baseChange A).conj e).toLocal v)
      (Field.AbsoluteGaloisGroup.adicArithFrob v)).trace A W =
    algebraMap R A ((ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).trace R V) := by
  change (((ρ.baseChange A).conj e).map _ _).trace A W = _
  rw [GaloisRep.map_conj, GaloisRep.baseChange_map, trace_baseChange_conj]

/-- Trace commutes with coefficient extension also after localization. -/
theorem trace_toLocal_baseChange {R A V : Type*} [CommRing R] [CommRing A]
    [TopologicalSpace R] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra R A] [ContinuousSMul R A]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (ρ : GaloisRep ℚ R V) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((ρ.baseChange A).toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).trace A _ =
    algebraMap R A ((ρ.toLocal v (Field.AbsoluteGaloisGroup.adicArithFrob v)).trace R V) := by
  change (((ρ.baseChange A).map _) _).trace A _ = _
  rw [GaloisRep.baseChange_map]
  exact LinearMap.trace_baseChange _ A

/-- For a two-dimensional endomorphism the trace is minus the coefficient of X. -/
theorem trace_eq_neg_coeff {K : Type*} [Field K]
    (f : Module.End K (Fin 2 → K)) : f.trace K _ = -f.charpoly.coeff 1 := by
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin 2)),
    ← LinearMap.charpoly_toMatrix f (Pi.basisFun K (Fin 2))]
  simpa using Matrix.trace_eq_neg_charpoly_coeff (LinearMap.toMatrix
    (Pi.basisFun K (Fin 2)) (Pi.basisFun K (Fin 2)) f)

/-- Any map from a finite domain over the p-adic integers to a characteristic-zero
field is injective, even without a specified scalar tower on the target. -/
theorem padic_domain_map_injective {p : ℕ} [Fact p.Prime]
    {R K : Type*} [CommRing R] [IsDomain R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] [Field K] [CharZero K] (f : R →+* K) :
    Function.Injective f := by
  let : Algebra R K := f.toAlgebra
  let : Algebra ℤ_[p] K := (f.comp (algebraMap ℤ_[p] R)).toAlgebra
  have : IsScalarTower ℤ_[p] R K := IsScalarTower.of_algebraMap_eq' rfl
  apply Algebra.IsAlgebraic.injective_tower_top (R := ℤ_[p]) R
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  by_contra hne
  have h := PadicInt.unitCoeff_spec hne
  have hu := (PadicInt.unitCoeff hne).isUnit.map (algebraMap ℤ_[p] K)
  have hnonzero : algebraMap ℤ_[p] K x ≠ 0 := by
    rw [h, map_mul, map_pow, map_natCast]
    exact mul_ne_zero hu.ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  exact hnonzero hx

/-- Distinct rational primes define distinct residue characteristics. -/
theorem prime_not_mem {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) :
    (p : 𝓞 ℚ) ∉ hq.toHeightOneSpectrumRingOfIntegersRat.asIdeal := by
  change ¬ Rat.ringOfIntegersEquiv (p : 𝓞 ℚ) ∈ Ideal.span {(q : ℤ)}
  rw [map_natCast, Ideal.mem_span_singleton]
  exact fun h ↦ hne ((Nat.prime_dvd_prime_iff_eq hq hp).mp (by exact_mod_cast h))

/-- Compatibility transports a prescribed rational Frobenius trace from one
member to another. Only the coefficient of X in the common polynomial is used. -/
theorem compatible_trace {E : Type*} [Field E] [NumberField E]
    (σ : GaloisRepFamily ℚ E 2) (hσ : σ.isCompatible)
    {ℓ : ℕ} (hℓ : Fact ℓ.Prime) (φ : E →+* AlgebraicClosure ℚ_[ℓ])
    (hφ : ∀ q (hq : q.Prime), 5 ≤ q → q ≠ ℓ →
      (σ hℓ φ |>.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
        (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).trace
          _ _ = 1 + q) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 ℚ)),
      ∀ {p : ℕ} (hp : Fact p.Prime) (ψ : E →+* AlgebraicClosure ℚ_[p])
        q (hq : q.Prime), 5 ≤ q → q ≠ ℓ → q ≠ p →
        hq.toHeightOneSpectrumRingOfIntegersRat ∉ S →
        (σ hp ψ |>.toLocal hq.toHeightOneSpectrumRingOfIntegersRat
          (Field.AbsoluteGaloisGroup.adicArithFrob hq.toHeightOneSpectrumRingOfIntegersRat)).trace
            _ _ = 1 + q := by
  obtain ⟨S, P, hP⟩ := hσ
  refine ⟨S, ?_⟩
  intro p hp ψ q hq hq5 hqℓ hqp hqS
  have hleft := (hP hℓ φ _ hqS (prime_not_mem hℓ.out hq hqℓ)).2
  have hright := (hP hp ψ _ hqS (prime_not_mem hp.out hq hqp)).2
  have hcoeff : -(P hq.toHeightOneSpectrumRingOfIntegersRat).coeff 1 = 1 + (q : E) := by
    apply φ.injective
    have ht := hφ q hq hq5 hqℓ
    rw [trace_eq_neg_coeff, hleft, Polynomial.coeff_map] at ht
    simpa using ht
  rw [trace_eq_neg_coeff, hright, Polynomial.coeff_map, ← map_neg, hcoeff]
  simp

end GaloisRepresentation.B5Inputs
