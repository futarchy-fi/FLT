/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.GaloisTowerCochainDescent

/-!
# Descent of an absolute multiplicative two-cocycle

A common open normal subgroup controls both the argument fibers and the
coefficient values. Its fixed field gives a finite relative cocycle whose
inflation is the original continuous cocycle, pointwise.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]

attribute [local instance] fieldUnitAction

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]

/-- Every continuous field-unit two-cocycle descends to a finite Galois fixed field. -/
theorem finiteRelative_cocycle_descent
    (c : C(Gal(L/K) × Gal(L/K), Additive Lˣ)) (hc : IsCocycle₂ c) :
    ∃ U : OpenNormalSubgroup Gal(L/K),
      let E := IntermediateField.fixedField U.toSubgroup
      let r := (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))
      ∃ d : Gal(E/K) × Gal(E/K) → Additive Eˣ, IsCocycle₂ d ∧
        ∀ g h, (galoisInflationCoefficients K L E).hom (d (r g, r h)) = c (g, h) := by
  obtain ⟨U, _, hcf, hcv, _, _⟩ := exists_towerRefinement_fibers
    (⊥ : Subgroup Gal(L/K)) c (ContinuousMap.const _ 0)
    ⟨⊤, by change (⊤ : Subgroup Gal(L/K)).Normal; infer_instance⟩
  let E := IntermediateField.fixedField U.toSubgroup
  let r := (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K))
  let i := (galoisInflationCoefficients K L E).hom.toLinearMap.toAddMonoidHom
  have hi : Function.Injective i := galoisInflationCoefficients_injective K L E
  have heq (g : Gal(L/K)) (x : Additive Eˣ) : i (r g • x) = g • i x :=
    Rep.hom_comm_apply (galoisInflationCoefficients K L E) g x
  have hker (g : Gal(L/K)) (hg : r g = 1) : g ∈ U := by
    change g ∈ U.toSubgroup
    rw [← galoisStage_restriction_ker K L U]
    exact hg
  have hfib (g h : Gal(L/K)) (he : r g = r h) : g⁻¹ * h ∈ U :=
    hker _ (by simp [he])
  have hcv' (g h : Gal(L/K)) : ∃ x, i x = c (g, h) :=
    galoisInflationCoefficients_fixed K L E _ (fun n hn => hcv n (hker n hn) _)
  obtain ⟨d, hd, hd'⟩ := exists_twoCocycle_descent_of_fibers r
    (AlgEquiv.restrictNormalHom_surjective L) i hi heq c hc
    (fun g h g' h' hg hh => hcf g h g' h' (hfib g g' hg) (hfib h h' hh)) hcv'
  exact ⟨U, d, hd, hd'⟩

end LocalClassFieldTheory
