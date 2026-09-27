/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.FiniteGaloisRealization
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.PowerFrobCover
public import FLT.GaloisRepresentation.HardlyRamified.Chebotarev.W2Statement

/-!
# Power-Frobenius covers of finite monoids

Leaf W3 of `docs/CHEBOTAREV_PLAN.md`: pass through the image in units to a
finite Galois extension, then assemble the power and Frobenius comparisons.
-/

@[expose] public section

namespace GaloisRepresentation.Chebotarev

/-- A continuous map to a finite discrete monoid factors through a finite
Galois extension, by applying G2 to its image in the group of units. -/
@[nolint unusedArguments]
theorem exists_finiteGalois_monoid_factorization
    {M : Type*} [Monoid M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (f : Field.absoluteGaloisGroup ℚ →ₜ* M) :
    ∃ (L : IntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L)
      (p : Gal(L/ℚ) →* M),
      ∀ g, p (AlgEquiv.restrictNormalHom L g) = f g := by
  let u := f.toMonoidHom.toHomUnits
  have hu : Continuous u := Units.continuous_iff.mpr
    ⟨f.continuous, f.continuous.comp continuous_inv⟩
  let π : Field.absoluteGaloisGroup ℚ →ₜ* u.range :=
    { u.rangeRestrict with continuous_toFun := hu.subtype_mk _ }
  let ι : u.range →* M := (Units.coeHom M).comp u.range.subtype
  obtain ⟨L, hfin, hgal, e, he⟩ :=
    exists_finiteGalois_realization π u.rangeRestrict_surjective
  exact ⟨L, hfin, hgal, ι.comp e.toMonoidHom, fun g ↦ congrArg ι (he g)⟩

/-- A generator of the automorphism group over the fixed field of `⟨g⟩`
has a nonnegative power whose restriction of scalars is `g`. -/
theorem exists_pow_restrictScalars_eq
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] (g : Gal(L/ℚ))
    (a : Gal(L/IntermediateField.fixedField (Subgroup.zpowers g)))
    (ha : Subgroup.zpowers a = ⊤) :
    ∃ n : ℕ, (AlgEquiv.restrictScalarsHom ℚ a) ^ n = g := by
  let H := Subgroup.zpowers g
  let g' := IntermediateField.subgroupEquivAlgEquiv H ⟨g, Subgroup.mem_zpowers g⟩
  have hg' : g' ∈ Subgroup.zpowers a := ha ▸ Subgroup.mem_top g'
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff g' a).mp
    (mem_powers_iff_mem_zpowers.mpr hg')
  refine ⟨n, ?_⟩
  have h := congrArg (AlgEquiv.restrictScalarsHom ℚ) hn
  rw [map_pow] at h
  exact h

end GaloisRepresentation.Chebotarev
