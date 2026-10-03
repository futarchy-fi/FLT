/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousCoefficientMaps

/-!
# Continuous restriction and its finite stages

A continuous group homomorphism pulls open normal stages back to open normal
stages. Restricting cochains commutes with inflation from these constructed stages.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace LocalClassFieldTheory

open CategoryTheory groupCohomology

variable {k G H M P : Type u} [CommRing k] [Group G] [Group H]
  [AddCommGroup M] [Module k M] [DistribMulAction H M] [SMulCommClass H k M]
  [AddCommGroup P] [Module k P] [DistribMulAction G P] [SMulCommClass G k P]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul H M]
  [TopologicalSpace P] [DiscreteTopology P] [ContinuousSMul G P]

local notation "RM" => Rep.of (Representation.ofDistribMulAction k H M)
local notation "RP" => Rep.of (Representation.ofDistribMulAction k G P)

/-- Pull back an open normal stage along the continuous group map. -/
def restrictionStage (f : G →* H) (hf : Continuous f) (N : OpenNormalSubgroup H) :
    OpenNormalSubgroup G :=
  ⟨N.toOpenSubgroup.comap f hf, by
    change (N.toSubgroup.comap f).Normal
    infer_instance⟩

/-- The ordinary group-and-coefficient map restricted to continuous cochains. -/
def continuousRestriction (f : G →* H) (hf : Continuous f) (φ : Rep.res f RM ⟶ RP) :
    continuousCochains k H M ⟶ continuousCochains k G P :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom
    ((((cochainsMap f φ).f n).hom.comp (continuousCochainModule k H M n).subtype
      ).codRestrict _ (fun c =>
        (continuous_of_discreteTopology (f := φ.hom)).comp
          (c.property.comp (continuous_pi fun i => hf.comp (continuous_apply i))))))
    (fun n => by
      ext c : 2
      apply Subtype.ext
      have h := (cochainsMap (A := RM) (B := RP) f φ).comm n (n + 1)
      rw [inhomogeneousCochains.d_def, inhomogeneousCochains.d_def] at h
      simpa only [continuousCochains, CochainComplex.of_d, continuousCochainD,
        ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        LinearMap.codRestrict_apply, Submodule.subtype_apply] using
        congrArg (fun g => g.hom c.val) h)

/-- Restriction evaluates by pulling back every group argument. -/
theorem continuousRestriction_apply (f : G →* H) (hf : Continuous f)
    (φ : Rep.res f RM ⟶ RP) (n : ℕ) (c : (continuousCochains k H M).X n) (x : Fin n → G) :
    (((continuousRestriction f hf φ).f n).hom c).val x = φ.hom (c.val (f ∘ x)) := rfl

/-- The coefficient map sends N-invariants to invariants of the pulled-back subgroup. -/
def restrictionInvariantMap (f : G →* H) (φ : Rep.res f RM ⟶ RP) (N : Subgroup H) :
    Representation.invariants ((RM).ρ.comp N.subtype) →ₗ[k]
      Representation.invariants ((RP).ρ.comp (N.comap f).subtype) :=
  (φ.hom.toLinearMap.comp (Representation.invariants ((RM).ρ.comp N.subtype)).subtype
    ).codRestrict _ (fun x g => by
      change (RP).ρ g.val (φ.hom x.val) = φ.hom x.val
      rw [← Rep.hom_comm_apply]
      exact congrArg φ.hom (x.property ⟨f g.val, g.property⟩))

/-- Restriction on the finite quotient complexes uses the constructed subgroup pullback. -/
def restrictionStageMap (f : G →* H) (hf : Continuous f) (φ : Rep.res f RM ⟶ RP)
    (N : OpenNormalSubgroup H) :
    (invariantStageDiagram k H M).obj N ⟶
      (invariantStageDiagram k G P).obj (restrictionStage f hf N) :=
  cochainsMap (QuotientGroup.map (N.toSubgroup.comap f) N.toSubgroup f (le_refl _))
    (Rep.ofHom ⟨restrictionInvariantMap f φ N.toSubgroup, fun g => by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N.toSubgroup.comap f) g
      ext x
      exact Rep.hom_comm_apply φ g x.val⟩)

/-- Inflation and restriction commute at the explicitly pulled-back finite stage. -/
theorem continuousRestriction_inflation (f : G →* H) (hf : Continuous f)
    (φ : Rep.res f RM ⟶ RP) (N : OpenNormalSubgroup H) :
    restrictionStageMap f hf φ N ≫ continuousStageInflation k G P (restrictionStage f hf N) =
      continuousStageInflation k H M N ≫ continuousRestriction f hf φ := by
  ext n c
  rfl

end LocalClassFieldTheory
