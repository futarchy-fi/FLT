/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.AtTwo
public import FLT.FreyCurve.Serre.LocalTorsion
public import FLT.FreyCurve.Serre.MultiplicativeQuotient
public import FLT.FreyCurve.Serre.ReducibleFiltration
public import FLT.GaloisRepresentation.HardlyRamified.Defs

/-!
# The rank-one quotient of Frey torsion at two

The Tate exponent quotient, transported by an unramified splitting twist,
gives the precise local condition at two in `IsHardlyRamified`.
-/

@[expose] public section

namespace GaloisRep

variable {K k V : Type*} [Field K] [Field k] [TopologicalSpace k]
  [DiscreteTopology k] [AddCommGroup V] [Module k V]

/-- A surjective functional transformed by signs determines a continuous quadratic quotient. -/
theorem exists_quadratic_quotient_of_signed_functional
    (ρ : GaloisRep K k V) (r : V →ₗ[k] k) (hr : Function.Surjective r)
    (hsign : ∀ g, (∀ v, r (ρ g v) = r v) ∨ (∀ v, r (ρ g v) = -r v)) :
    ∃ δ : GaloisRep K k k,
      (∀ g v, r (ρ g v) = δ g (r v)) ∧
      (∀ g, δ g * δ g = 1) ∧
      (∀ g, (∀ v, r (ρ g v) = r v) → δ g = 1) := by
  obtain ⟨w, hw⟩ := hr 1
  let c (g : Field.absoluteGaloisGroup K) := r (ρ g w)
  have hc (g : Field.absoluteGaloisGroup K) (v : V) : r (ρ g v) = c g * r v := by
    rcases hsign g with h | h <;> simp [c, h, hw]
  have hc1 : c 1 = 1 := by simp [c, hw]
  have hcmul (g h : Field.absoluteGaloisGroup K) : c (g * h) = c g * c h := by
    change r (ρ (g * h) w) = _
    rw [map_mul]
    exact hc g (ρ h w)
  let d : Representation k (Field.absoluteGaloisGroup K) k := {
    toFun := fun g ↦ c g • (1 : Module.End k k)
    map_one' := by simp [hc1]
    map_mul' := fun g h ↦ by
      apply LinearMap.ext
      intro x
      simp [hcmul, mul_assoc, mul_left_comm] }
  let δ : GaloisRep K k k := ofDetermined ρ d (by
    intro g h hgh
    change c g • (1 : Module.End k k) = c h • (1 : Module.End k k)
    simp only [c, hgh])
  have hd (g : Field.absoluteGaloisGroup K) (x : k) : δ g x = c g * x := rfl
  refine ⟨δ, ?_, ?_, ?_⟩
  · intro g v
    rw [hd]
    exact hc g v
  · intro g
    apply LinearMap.ext
    intro x
    change δ g (δ g x) = x
    rw [hd, hd]
    rcases hsign g with h | h <;> simp [c, h, hw]
  · intro g h
    apply LinearMap.ext
    intro x
    rw [hd]
    simp [c, h, hw]

end GaloisRep

open ValuativeRel GaloisRepresentation
open scoped Pointwise

private theorem twoAdicClosure_comap :
    (Z2bar.comap (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))).toSubring =
      (algebraMap 𝒪[ℚ_[2]] ℚ_[2]).range := by
  rw [Subring.algebraMap_def, Subring.range_subtype]
  ext x
  change Valued.v (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x) ≤ 1 ↔
    ValuativeRel.valuation ℚ_[2] x ≤ 1
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation ℚ_[2]) Padic.mulValuation).le_one_iff_le_one]
  change ‖algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]) x‖₊ ≤ 1 ↔ _
  rw [← NNReal.coe_le_coe]
  simp only [coe_nnnorm, NNReal.coe_one, norm_algebraMap']
  have h := Padic.norm_lt_norm_iff_mulValuation_lt (x := (1 : ℚ_[2])) (y := x)
  simpa only [norm_one, map_one, not_lt] using not_congr h

private noncomputable def twoAdicDecomposition (σ : Field.absoluteGaloisGroup ℚ_[2]) :
    Z2bar.decompositionSubgroup ℚ_[2] :=
  ⟨σ, by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ‖σ y‖₊ ≤ 1
      change ‖y‖₊ ≤ 1 at hy
      have hh : ‖σ y‖₊ = ‖y‖₊ := by
        apply NNReal.coe_injective
        exact (spectralNorm_eq_of_equiv σ y).symm
      rwa [hh]
    · intro hx
      refine ⟨σ.symm x, ?_, σ.apply_symm_apply x⟩
      change ‖σ.symm x‖₊ ≤ 1
      change ‖x‖₊ ≤ 1 at hx
      have hh : ‖σ.symm x‖₊ = ‖x‖₊ := by
        apply NNReal.coe_injective
        exact (spectralNorm_eq_of_equiv σ.symm x).symm
      rwa [hh]⟩

private theorem twoAdicDecomposition_mem_inertia (σ : Field.absoluteGaloisGroup ℚ_[2])
    (hσ : σ ∈ AddSubgroup.inertia
      ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
      (Field.absoluteGaloisGroup ℚ_[2])) :
    twoAdicDecomposition σ ∈ Z2bar.inertiaSubgroup ℚ_[2] := by
  change MulSemiringAction.toRingAut _ _ (twoAdicDecomposition σ) = 1
  apply RingEquiv.ext
  intro x
  obtain ⟨x,rfl⟩ := IsLocalRing.residue_surjective x
  change (twoAdicDecomposition σ) • IsLocalRing.residue _ x = IsLocalRing.residue _ x
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply sub_eq_zero.mp
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hσ x

set_option backward.isDefEq.respectTransparency false in
/-- The surjective rank-one quotient at two required by `IsHardlyRamified`.
Its character is unramified and its square is trivial. -/
theorem FreyCurve.torsion_quotient_at_two (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ∃ (π : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p
        →ₗ[ZMod P.p] ZMod P.p) (_ : Function.Surjective π)
      (δ : GaloisRep ℚ_[2] (ZMod P.p) (ZMod P.p)),
      ∀ (g : Field.absoluteGaloisGroup ℚ_[2]) v,
        π ((P.freyCurve.galoisRep P.p P.hppos).map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
        (AddSubgroup.inertia
          ((IsLocalRing.maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar)
          (Field.absoluteGaloisGroup ℚ_[2]) ≤ δ.ker) ∧
        (∀ g : Field.absoluteGaloisGroup ℚ_[2], δ g * δ g = 1) := by
  classical
  let : Fact P.p.Prime := ⟨P.pp⟩
  let E := P.freyCurve.baseChange ℚ_[2]
  let : E.HasMultiplicativeReduction 𝒪[ℚ_[2]] :=
    FreyCurve.hasMultiplicativeReduction_at_two P
  obtain ⟨r, hr, hinertia, hsign⟩ :=
    E.exists_signed_inertia_invariant_torsion_quotient Z2bar twoAdicClosure_comap P.p
  let r' : (E.map (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2]))).nTorsion P.p
      →+ ZMod P.p := r
  let ψ := P.freyCurve.geometricTorsionBaseChange (L := ℚ_[2]) P.p
  let π := (r'.toZModLinearMap P.p).comp ψ
  have hπ : Function.Surjective π :=
    hr.comp (P.freyCurve.geometricTorsionBaseChange_bijective (L := ℚ_[2]) P.hppos).2
  let ρ := (P.freyCurve.galoisRep P.p P.hppos).map (algebraMap ℚ ℚ_[2])
  have hs : ∀ g, (∀ v, π (ρ g v) = π v) ∨ (∀ v, π (ρ g v) = -π v) := by
    intro g
    rcases hsign g with h | h
    · left
      intro v
      change r (ψ (ρ g v)) = r (ψ v)
      rw [P.freyCurve.geometricTorsionBaseChange_equivariant P.p P.hppos g]
      exact h _ _ rfl
    · right
      intro v
      change r (ψ (ρ g v)) = -r (ψ v)
      rw [P.freyCurve.geometricTorsionBaseChange_equivariant P.p P.hppos g]
      exact h _ _ rfl
  obtain ⟨δ, heq, hsq, htriv⟩ := ρ.exists_quadratic_quotient_of_signed_functional π hπ hs
  refine ⟨π, hπ, δ, fun g v ↦ ⟨heq g v, ?_, hsq⟩⟩
  intro σ hσ
  apply htriv σ
  intro v
  change r (ψ (ρ σ v)) = r (ψ v)
  rw [P.freyCurve.geometricTorsionBaseChange_equivariant P.p P.hppos σ]
  exact hinertia (twoAdicDecomposition σ) (twoAdicDecomposition_mem_inertia σ hσ) _ _ rfl
