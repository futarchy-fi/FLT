/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.ContinuousHilbert90

/-!
# The topology on a Galois restriction kernel

Restriction of scalars is continuous for the Krull topologies. This allows
continuous cocycles on a restriction kernel to use continuous Hilbert 90
over the intermediate field.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

set_option backward.isDefEq.respectTransparency false

open scoped Topology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (E : IntermediateField K L)

/-- Enlarging the base field gives a continuous map between Krull Galois groups. -/
theorem galoisRestrictScalars_continuous :
    Continuous (AlgEquiv.restrictScalarsHom K : Gal(L/E) →* Gal(L/K)) := by
  classical
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro V hV
  rw [map_one, krullTopology_mem_nhds_one_iff] at hV
  obtain ⟨F, hF, hFV⟩ := hV
  let := hF
  let b := Module.finBasis K F
  let S : Set L := Set.range (fun j => (b j : L))
  let T := IntermediateField.adjoin E S
  let : Finite S := Set.finite_range _ |>.to_subtype
  let : FiniteDimensional E T := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  apply Filter.mem_of_superset (T.fixingSubgroup_isOpen.mem_nhds T.fixingSubgroup.one_mem)
  intro g hg
  apply hFV
  change g.restrictScalars K ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  have he : (g.restrictScalars K).toLinearMap.comp F.val.toLinearMap = F.val.toLinearMap := by
    apply b.ext
    intro j
    change g ∈ T.fixingSubgroup at hg
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.subset_adjoin E S ⟨j, rfl⟩)
  intro x hx
  exact LinearMap.congr_fun he ⟨x, hx⟩

variable [IsGalois K E]

/-- The kernel of restriction is the Galois group over the intermediate field. -/
def galoisRestrictionKernelEquiv :
    (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker ≃* Gal(L/E) :=
  (MulEquiv.subgroupCongr E.restrictNormalHom_ker).trans
    (IntermediateField.fixingSubgroupEquiv E)

/-- The inverse kernel identification is continuous. -/
theorem galoisRestrictionKernelEquiv_symm_continuous :
    Continuous (galoisRestrictionKernelEquiv K L E).symm :=
  (galoisRestrictScalars_continuous K L E).subtype_mk _

attribute [local instance] fieldUnitAction

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]

/-- Continuous Hilbert 90 for the actual restriction kernel and its inherited action. -/
theorem galoisRestrictionKernel_hilbert90
    (z : GaloisRepresentation.Extensions.ContinuousCocycle
      (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker (Additive Lˣ)) :
    ∃ a : Additive Lˣ, ∀ n, z.val n = n • a - a := by
  let e := galoisRestrictionKernelEquiv K L E
  let c : GaloisRepresentation.Extensions.ContinuousCocycle Gal(L/E) (Additive Lˣ) :=
    ⟨⟨fun g => z.val (e.symm g), z.val.continuous.comp
      (galoisRestrictionKernelEquiv_symm_continuous K L E)⟩, fun g h => by
      change z.val (e.symm (g * h)) = _
      rw [map_mul, z.property]
      rfl⟩
  obtain ⟨a, ha⟩ := continuousFieldUnitCocycle_eq_coboundary E L c
  refine ⟨a, fun n => ?_⟩
  have h := ha (e n)
  change z.val (e.symm (e n)) = _ at h
  change z.val (e.symm (e n)) = n • a - a at h
  simpa only [MulEquiv.symm_apply_apply] using h

end LocalClassFieldTheory
