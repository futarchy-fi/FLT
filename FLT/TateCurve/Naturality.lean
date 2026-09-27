/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import FLT.TateCurve.Points

/-!
# Naturality of the Tate point map

Over local field extensions, the convergent coordinate formulas give a point on
the base change of the original Tate curve. Continuous algebra homomorphisms
commute with this map, including at the identity class.
-/

@[expose] public section

open ValuativeRel
open scoped WeierstrassCurve.Affine

namespace TateCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [DecidableEq L]

/-- The Tate point map over an extension, viewed on the base change of the original curve. -/
noncomputable def uniformizationPointOver (q : Kˣ) (hq : valuation K (q : K) < 1)
    (u : Lˣ) : ((WeierstrassCurve.tateCurve (q : K))⁄L).Point :=
  WeierstrassCurve.Affine.Point.equivOfEq (WeierstrassCurve.tateCurve_baseChange
    (l := L) (q : K) hq).symm
    (uniformizationPoint (Units.map (algebraMap K L).toMonoidHom q)
      (valuation_algebraMap_lt_one hq) u)

variable {L}
variable {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [DecidableEq M]

/-- An injective map of groups reflects membership in the cyclic subgroup of a mapped element. -/
theorem map_mem_zpowers_iff {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (q u : G) :
    f u ∈ Subgroup.zpowers (f q) ↔ u ∈ Subgroup.zpowers q := by
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hf (by simpa using hn)⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, (map_zpow f q n).symm⟩

/-- Continuous algebra homomorphisms commute with the constructed point map on Tate curves. -/
theorem map_uniformizationPointOver (f : L →ₐ[K] M) (hf : Continuous f)
    (q : Kˣ) (hq : valuation K (q : K) < 1) (u : Lˣ) :
    WeierstrassCurve.Affine.Point.map f (uniformizationPointOver L q hq u) =
      uniformizationPointOver M q hq (Units.map f.toRingHom.toMonoidHom u) := by
  let : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  have : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  have hqmap : Units.map f.toRingHom.toMonoidHom
      (Units.map (algebraMap K L).toMonoidHom q) =
      Units.map (algebraMap K M).toMonoidHom q := by
    ext
    exact f.commutes (q : K)
  have hmem : Units.map f.toRingHom.toMonoidHom u ∈
      Subgroup.zpowers (Units.map (algebraMap K M).toMonoidHom q) ↔
      u ∈ Subgroup.zpowers (Units.map (algebraMap K L).toMonoidHom q) := by
    rw [← hqmap]
    exact map_mem_zpowers_iff (Units.map f.toRingHom.toMonoidHom)
      (Units.map_injective f.injective) _ _
  by_cases hu : u ∈ Subgroup.zpowers (Units.map (algebraMap K L).toMonoidHom q)
  · simp only [uniformizationPointOver, uniformizationPoint, dite_eq_left hu,
      dite_eq_left (hmem.mpr hu), ← WeierstrassCurve.Affine.Point.zero_def]
    erw [AddEquiv.map_zero, AddEquiv.map_zero, map_zero]
  · simp only [uniformizationPointOver, uniformizationPoint, dite_eq_right hu,
      dite_eq_right (mt hmem.mp hu)]
    erw [WeierstrassCurve.Affine.Point.equivOfEq_some,
      WeierstrassCurve.Affine.Point.equivOfEq_some,
      WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · simpa using map_tateX f.toRingHom hf
        ((map_ne_zero (algebraMap K L)).mpr q.ne_zero) u.ne_zero
        (tendsto_pow_nhds_zero (valuation_algebraMap_lt_one (l := L) hq))
    · simpa using map_tateY f.toRingHom hf
        ((map_ne_zero (algebraMap K L)).mpr q.ne_zero) u.ne_zero
        (tendsto_pow_nhds_zero (valuation_algebraMap_lt_one (l := L) hq))

/-- Continuous Galois automorphisms act equivariantly on the constructed Tate point map. -/
theorem uniformizationPointOver_galois (σ : L ≃ₐ[K] L) (hσ : Continuous σ)
    (q : Kˣ) (hq : valuation K (q : K) < 1) (u : Lˣ) :
    WeierstrassCurve.Affine.Point.map σ.toAlgHom (uniformizationPointOver L q hq u) =
      uniformizationPointOver L q hq (Units.map σ.toAlgHom.toRingHom.toMonoidHom u) :=
  map_uniformizationPointOver σ.toAlgHom hσ q hq u

end TateCurve
