/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousStageDiagram

/-!
# Coefficient maps on continuous cochains

Equivariant linear maps between discrete coefficients preserve continuity.
The maps restrict the ordinary coefficient maps and commute with stage inflation.
-/

@[expose] public noncomputable section

universe u

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G M P Q : Type u} [CommRing k] [Group G]
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [AddCommGroup Q] [Module k Q] [DistribMulAction G Q] [SMulCommClass G k Q]

local notation "RM" => Rep.of (Representation.ofDistribMulAction k G M)
local notation "RP" => Rep.of (Representation.ofDistribMulAction k G P)
local notation "RQ" => Rep.of (Representation.ofDistribMulAction k G Q)

/-- A coefficient map restricts to the invariants of each subgroup. -/
def invariantCoefficientMap (φ : RM ⟶ RP) (N : Subgroup G) :
    Representation.invariants ((RM).ρ.comp N.subtype) →ₗ[k]
      Representation.invariants ((RP).ρ.comp N.subtype) :=
  (φ.hom.toLinearMap.comp (Representation.invariants ((RM).ρ.comp N.subtype)).subtype
    ).codRestrict _ (fun x g => by
      change (RP).ρ g.val (φ.hom x.val) = φ.hom x.val
      rw [← Rep.hom_comm_apply]
      exact congrArg φ.hom (x.property g))

/-- Coefficient maps on the quotient representations' actual complexes. -/
def invariantStageCoefficientMap (φ : RM ⟶ RP) (N : Subgroup G) [N.Normal] :
    inhomogeneousCochains (Rep.of ((RM).ρ.quotientToInvariants N)) ⟶
      inhomogeneousCochains (Rep.of ((RP).ρ.quotientToInvariants N)) :=
  cochainsMap (MonoidHom.id _) (Rep.ofHom ⟨invariantCoefficientMap φ N, fun g => by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g
    ext x
    exact Rep.hom_comm_apply φ g x.val⟩)

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]
  [TopologicalSpace Q] [DiscreteTopology Q] [ContinuousSMul G Q]

set_option backward.isDefEq.respectTransparency false in
/-- The ordinary coefficient cochain map, restricted to continuous cochains. -/
def continuousCoefficientMap (φ : RM ⟶ RP) :
    continuousCochains k G M ⟶ continuousCochains k G P :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    ((φ.hom.toLinearMap.compLeft (Fin n → G)).comp
      (continuousCochainModule k G M n).subtype |>.codRestrict _
        (fun c => (continuous_of_discreteTopology (f := φ.hom)).comp c.property)))
    (fun n => by
      ext c : 2
      apply Subtype.ext
      have h := (cochainsMap (A := RM) (B := RP) (MonoidHom.id G) φ).comm n (n + 1)
      rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def] at h
      have he := congrArg (fun f => f.hom c.val) h
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
        cochainsMap_id_f_hom_eq_compLeft, continuousCochains, CochainComplex.of_d,
        continuousCochainD, ModuleCat.hom_ofHom, LinearMap.codRestrict_apply,
        LinearMap.coe_comp, Submodule.coe_subtype] using he)


/-- Evaluation is pointwise application of the coefficient map. -/
theorem continuousCoefficientMap_apply (φ : RM ⟶ RP) (n : ℕ)
    (c : (continuousCochains k G M).X n) (x : Fin n → G) :
    (((continuousCoefficientMap φ).f n).hom c).val x = φ.hom (c.val x) := rfl

/-- Identity coefficients induce the identity cochain map. -/
@[simp] theorem continuousCoefficientMap_id :
    continuousCoefficientMap (𝟙 (RM)) = 𝟙 _ := by
  ext n c
  rfl

/-- Composition of coefficients induces composition of continuous cochain maps. -/
theorem continuousCoefficientMap_comp (φ : RM ⟶ RP) (ψ : RP ⟶ RQ) :
    continuousCoefficientMap (φ ≫ ψ) =
      continuousCoefficientMap φ ≫ continuousCoefficientMap ψ := by
  ext n c
  rfl

/-- Forgetting continuity gives Mathlib's coefficient cochain map. -/
theorem continuousCoefficientMap_inclusion (φ : RM ⟶ RP) :
    continuousCoefficientMap φ ≫ continuousCochainsInclusion k G P =
      continuousCochainsInclusion k G M ≫ cochainsMap (MonoidHom.id G) φ := by
  ext n c
  rfl

/-- Coefficient maps commute with inflation from every open normal stage. -/
theorem continuousCoefficientMap_inflation (φ : RM ⟶ RP) (N : OpenNormalSubgroup G) :
    invariantStageCoefficientMap φ N.toSubgroup ≫ continuousStageInflation k G P N =
      continuousStageInflation k G M N ≫ continuousCoefficientMap φ := by
  ext n c
  rfl

end LocalClassFieldTheory
