/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.Slop.Ribet_Lemma.LatticeGaloisRep

/-!
# The quotient at two on a stable lattice

A quotient functional extends to the fraction field. Its image on any other
lattice is a nonzero principal fractional ideal; choosing its generator gives
a surjective integral functional with the same local character.
-/

@[expose] public section

open Module IsLocalRing
open scoped TensorProduct Topology nonZeroDivisors

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ThreeAdicPlan

variable {O K W : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]

/-- An integral functional on a lattice extends to the ambient vector space. -/
theorem exists_lattice_functional_extension (Λ : Submodule O W)
    [Submodule.IsLattice K Λ] (π : Λ →ₗ[O] O) :
    ∃ f : W →ₗ[K] K, ∀ x : Λ, f x = algebraMap O K (π x) := by
  classical
  let b := Module.Free.chooseBasis O Λ
  let f := (b.extendOfIsLattice K).constr K (fun i => algebraMap O K (π (b i)))
  refine ⟨f, ?_⟩
  have h : (f.restrictScalars O).comp Λ.subtype = (Algebra.linearMap O K).comp π := by
    apply b.ext
    intro i
    change f (b i : W) = algebraMap O K (π (b i))
    rw [← Basis.extendOfIsLattice_apply K b i]
    exact Basis.constr_basis _ _ _ _
  exact LinearMap.congr_fun h

/-- Dividing a nonzero functional by a generator of its lattice image gives
an integral surjection. -/
theorem exists_primitive_lattice_functional (Λ : Submodule O W)
    [Submodule.IsLattice K Λ] (f : W →ₗ[K] K) (hf : f ≠ 0) :
    ∃ (π : Λ →ₗ[O] O) (a : K), a ≠ 0 ∧ Function.Surjective π ∧
      ∀ x : Λ, f x = algebraMap O K (π x) * a := by
  classical
  let p := (f.restrictScalars O).comp Λ.subtype
  let I : FractionalIdeal O⁰ K :=
    ⟨LinearMap.range p, FractionalIdeal.isFractional_of_fg
      (by simpa only [Submodule.map_top] using (Module.Finite.fg_top.map p))⟩
  let a := Submodule.IsPrincipal.generator (I : Submodule O K)
  have ha : a ≠ 0 := by
    intro ha
    have hI : (I : Submodule O K) = ⊥ :=
      (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mpr ha
    apply hf
    apply (Module.Free.chooseBasis O Λ).extendOfIsLattice K |>.ext
    intro i
    have hm : p (Module.Free.chooseBasis O Λ i) ∈ (I : Submodule O K) :=
      LinearMap.mem_range_self p _
    rw [hI] at hm
    simpa [p] using hm
  let q : O →ₗ[O] (I : Submodule O K) :=
    LinearMap.toSpanSingleton O _ ⟨a, Submodule.IsPrincipal.generator_mem _⟩
  have hq : Function.Bijective q := by
    constructor
    · intro r s hrs
      apply IsFractionRing.injective O K
      have he : algebraMap O K r * a = algebraMap O K s * a :=
        by simpa [q, Algebra.smul_def] using congrArg Subtype.val hrs
      exact mul_right_cancel₀ ha he
    · intro y
      obtain ⟨r, hr⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator
        (I : Submodule O K)).mp y.property
      exact ⟨r, Subtype.ext hr.symm⟩
  let e := LinearEquiv.ofBijective q hq
  let π := e.symm.toLinearMap.comp p.rangeRestrict
  refine ⟨π, a, ha, e.symm.surjective.comp p.surjective_rangeRestrict, ?_⟩
  intro x
  have he := congrArg Subtype.val (e.apply_symm_apply (p.rangeRestrict x))
  change (π x) • a = f x at he
  simpa only [Algebra.smul_def] using he.symm

variable [TopologicalSpace O] [IsTopologicalRing O]
  [TopologicalSpace K] [IsTopologicalRing K]

/-- Exactly the quotient-at-two clause of `IsHardlyRamified`. -/
@[nolint unusedArguments]
def TameTwo {R V : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup V] [Module R V] (ρ : GaloisRep ℚ R V) : Prop :=
  ∃ (π : V →ₗ[R] R) (_ : Function.Surjective π) (δ : GaloisRep ℚ_[2] R R),
    ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) (v : V),
      π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
      (AddSubgroup.inertia
        ((maximalIdeal GaloisRepresentation.Z2bar).toAddSubgroup :
          AddSubgroup GaloisRepresentation.Z2bar)
        (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
      (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1)

/-- The quotient-at-two condition is independent of the stable lattice.
The quotient uses the same continuous local character as the original lattice. -/
theorem tame_two_of_stable_lattice (ρK : GaloisRep ℚ K W)
    (Λ₀ Λ : Submodule O W)
    (h₀ : StableLattice.IsStableLattice ρK.toRepresentation Λ₀)
    (hΛ : StableLattice.IsStableLattice ρK.toRepresentation Λ)
    (hOK : Topology.IsInducing (algebraMap O K))
    (hπ : TameTwo (latticeGaloisRep ρK Λ₀ h₀ hOK)) :
    TameTwo (latticeGaloisRep ρK Λ hΛ hOK) := by
  classical
  let := h₀.isLattice
  let := hΛ.isLattice
  obtain ⟨π₀, hπ₀, δ, hδ⟩ := hπ
  obtain ⟨f, hf⟩ := exists_lattice_functional_extension (K := K) Λ₀ π₀
  have hf0 : f ≠ 0 := by
    intro hzero
    obtain ⟨x, hx⟩ := hπ₀ 1
    have hx' := hf x
    simp [hzero, hx] at hx'
  obtain ⟨π, a, ha, hsurj, hfa⟩ := exists_primitive_lattice_functional Λ f hf0
  have hδmul (g : Field.absoluteGaloisGroup ℚ_[2]) (r : O) :
      δ g r = δ g 1 * r := by
    simpa [mul_comm] using (δ g).map_smul r (1 : O)
  have heq (g : Field.absoluteGaloisGroup ℚ_[2]) :
      f.comp (ρK.map (algebraMap ℚ ℚ_[2]) g) =
        algebraMap O K (δ g 1) • f := by
    apply ((Module.Free.chooseBasis O Λ₀).extendOfIsLattice K).ext
    intro i
    simp only [Basis.extendOfIsLattice_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, smul_eq_mul]
    let x := Module.Free.chooseBasis O Λ₀ i
    calc
      f (ρK.map (algebraMap ℚ ℚ_[2]) g (x : W)) =
          algebraMap O K (π₀ ((latticeGaloisRep ρK Λ₀ h₀ hOK).map
            (algebraMap ℚ ℚ_[2]) g x)) :=
            hf ((latticeGaloisRep ρK Λ₀ h₀ hOK).map (algebraMap ℚ ℚ_[2]) g x)
      _ = algebraMap O K (δ g 1) * f x := by
        rw [(hδ g x).1, hδmul, map_mul, hf]
  refine ⟨π, hsurj, δ, ?_⟩
  intro g x
  refine ⟨?_, (hδ 1 0).2⟩
  apply IsFractionRing.injective O K
  apply mul_right_cancel₀ ha
  calc
    algebraMap O K (π ((latticeGaloisRep ρK Λ hΛ hOK).map
        (algebraMap ℚ ℚ_[2]) g x)) * a =
        f (ρK.map (algebraMap ℚ ℚ_[2]) g (x : W)) := (hfa _).symm
    _ = algebraMap O K (δ g 1) * f x := LinearMap.congr_fun (heq g) x
    _ = algebraMap O K (δ g (π x)) * a := by
      rw [hfa, hδmul g (π x), map_mul, mul_assoc]

end ThreeAdicPlan
