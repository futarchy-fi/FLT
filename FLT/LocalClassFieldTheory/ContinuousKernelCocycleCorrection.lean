/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteSubgroupCocycleCorrection
public import FLT.LocalClassFieldTheory.GaloisTowerCochainDescent

/-!
# Continuous correction through a finite Galois tower

Descend the cocycle and restricted boundary to one finite stage, correct
there using Hilbert 90, and inflate the correcting cochain. Its continuity
comes from a finite Galois quotient, not a section of a profinite quotient.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

/-- Correct a continuous two-cochain by a continuous differential. -/
def continuousCorrectTwoCocycle {G M : Type*} [Group G] [AddCommGroup M]
    [DistribMulAction G M] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]
    (c : C(G × G, M)) (b : C(G, M)) : C(G × G, M) :=
  ⟨correctTwoCocycle c b, c.continuous.sub
    (((continuous_fst.smul (b.continuous.comp continuous_snd)).sub
      (b.continuous.comp (continuous_fst.mul continuous_snd))).add
      (b.continuous.comp continuous_fst))⟩

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] fieldUnitAction

local notation "N" => (MonoidHom.ker (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)))

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]

/-- A restricted continuous boundary can be removed by a global continuous correction. -/
theorem continuousKernelCocycleCorrection
    (c : C(Gal(L/K) × Gal(L/K), Additive Lˣ)) (hc : IsCocycle₂ c)
    (b : C(N, Additive Lˣ))
    (hb : ∀ n m : N, c (n, m) = n • b m - b (n * m) + b n) :
    ∃ a : C(Gal(L/K), Additive Lˣ),
      (∀ n : N, ∀ g, correctTwoCocycle c a (n, g) = 0) ∧
      (∀ g, ∀ n : N, correctTwoCocycle c a (g, n) = 0) := by
  obtain ⟨U₀, _⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := Gal(L/K)) isOpen_univ (Set.mem_univ 1)
  obtain ⟨U, _, d, hd, a, hd', _, ha⟩ := galoisTowerCochainDescent K L E c hc b hb U₀
  let F := IntermediateField.fixedField U.toSubgroup
  let : FiniteDimensional K F := galoisOpenStage_fixedField_finite K L U
  let r := (AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K))
  let S := (N).map r
  let : S.Normal := Subgroup.Normal.map inferInstance r (AlgEquiv.restrictNormalHom_surjective L)
  obtain ⟨v, _, vl, vr⟩ := finiteSubgroupCocycleCorrection K F S d hd a ha
  let i := (galoisInflationCoefficients K L F).hom.toLinearMap.toAddMonoidHom
  let v' : C(Gal(L/K), Additive Lˣ) := ⟨fun g => i (v (r g)),
    (continuous_of_discreteTopology (f := fun q => i (v q))).comp
      (InfiniteGalois.restrictNormalHom_continuous F)⟩
  have heq (g : Gal(L/K)) (p : Additive Fˣ) : i (r g • p) = g • i p :=
    Rep.hom_comm_apply (galoisInflationCoefficients K L F) g p
  have hv (g h : Gal(L/K)) : correctTwoCocycle c v' (g, h) =
      i (correctTwoCocycle d v (r g, r h)) := by
    change c (g, h) - (g • i (v (r h)) - i (v (r (g * h))) + i (v (r g))) = _
    simp only [correctTwoCocycle, map_sub, map_add, heq, ← map_mul]
    exact congrArg (fun z => z - (g • i (v (r h)) - i (v (r (g * h))) + i (v (r g))))
      (hd' g h).symm
  refine ⟨v', ?_, ?_⟩
  · intro n g
    rw [hv]
    exact (congrArg i (vl (subgroupImageHom r N n) (r g))).trans (map_zero i)
  · intro g n
    rw [hv]
    exact (congrArg i (vr (r g) (subgroupImageHom r N n))).trans (map_zero i)

end LocalClassFieldTheory
