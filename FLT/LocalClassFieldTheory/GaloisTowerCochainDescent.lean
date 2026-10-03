/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.GaloisKernelRestriction
public import FLT.LocalClassFieldTheory.RestrictedCochainDescent
public import FLT.LocalClassFieldTheory.TowerRefinementFibers

/-!
# Compatible finite Galois descent of a cocycle and boundary

The common open normal subgroup supplies a finite Galois fixed field.
Both cochains descend with actual units of that field as coefficients.
The restricted boundary descends to the image of the original kernel,
and its boundary equation is proved at this same finite stage.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (E : IntermediateField K L) [IsGalois K E]

attribute [local instance] fieldUnitAction

local notation "N" => (MonoidHom.ker (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)))

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]

omit [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)] in
/-- The fixed field of a refinement has exactly that subgroup as restriction kernel. -/
theorem galoisStage_restriction_ker (U : OpenNormalSubgroup Gal(L/K)) :
    (AlgEquiv.restrictNormalHom (IntermediateField.fixedField U.toSubgroup) :
      Gal(L/K) →* Gal(IntermediateField.fixedField U.toSubgroup/K)).ker = U.toSubgroup := by
  rw [IntermediateField.restrictNormalHom_ker]
  exact InfiniteGalois.fixingSubgroup_fixedField (galoisOpenStageClosed K L U)

/-- Simultaneously descend a two-cocycle and a bounding cochain on the restriction kernel. -/
theorem galoisTowerCochainDescent
    (c : C(Gal(L/K) × Gal(L/K), Additive Lˣ)) (hc : IsCocycle₂ c)
    (b : C(N, Additive Lˣ))
    (hb : ∀ n m : N, c (n, m) = n • b m - b (n * m) + b n)
    (U₀ : OpenNormalSubgroup Gal(L/K)) :
    ∃ U : OpenNormalSubgroup Gal(L/K), U ≤ U₀ ∧
      let F := IntermediateField.fixedField U.toSubgroup
      let r := (AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K))
      ∃ d : Gal(F/K) × Gal(F/K) → Additive Fˣ, IsCocycle₂ d ∧
        ∃ a : (N).map r → Additive Fˣ,
          (∀ g h, (galoisInflationCoefficients K L F).hom (d (r g, r h)) = c (g, h)) ∧
          (∀ n, (galoisInflationCoefficients K L F).hom (a (subgroupImageHom r N n)) = b n) ∧
          ∀ n m : (N).map r, d (n, m) = n • a m - a (n * m) + a n := by
  obtain ⟨U, hU, hcf, hcv, hbf, hbv⟩ := exists_towerRefinement_fibers N c b U₀
  let F := IntermediateField.fixedField U.toSubgroup
  let r := (AlgEquiv.restrictNormalHom F : Gal(L/K) →* Gal(F/K))
  let i := (galoisInflationCoefficients K L F).hom.toLinearMap.toAddMonoidHom
  have hi : Function.Injective i := galoisInflationCoefficients_injective K L F
  have heq (g : Gal(L/K)) (p : Additive Fˣ) : i (r g • p) = g • i p :=
    Rep.hom_comm_apply (galoisInflationCoefficients K L F) g p
  have hker (g : Gal(L/K)) (hg : r g = 1) : g ∈ U := by
    change g ∈ U.toSubgroup
    rw [← galoisStage_restriction_ker K L U]
    exact hg
  have hfib (g h : Gal(L/K)) (he : r g = r h) : g⁻¹ * h ∈ U :=
    hker _ (by simp [he])
  have hcv' (g h : Gal(L/K)) : ∃ p, i p = c (g, h) :=
    galoisInflationCoefficients_fixed K L F _ (fun n hn => hcv n (hker n hn) _)
  obtain ⟨d, hd, hd'⟩ := exists_twoCocycle_descent_of_fibers r
    (AlgEquiv.restrictNormalHom_surjective L) i hi heq c hc
    (fun g h g' h' hg hh => hcf g h g' h' (hfib g g' hg) (hfib h h' hh)) hcv'
  have hbv' (n : N) : ∃ p, i p = b n :=
    galoisInflationCoefficients_fixed K L F _ (fun g hg => hbv g (hker g hg) n)
  obtain ⟨a, ha⟩ := exists_descended_subgroup_cochain r N i b
    (fun n m he => hbf n m (hfib n m he)) hbv'
  exact ⟨U, hU, d, hd, a, hd', ha, descended_subgroup_boundary r N i hi heq c b hb d hd' a ha⟩

end LocalClassFieldTheory
