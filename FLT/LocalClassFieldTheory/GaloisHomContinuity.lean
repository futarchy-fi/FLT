/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.Galois.Profinite

/-!
# Continuity of Galois restriction through a field embedding

Equivariance of an injective field map gives continuity for the Krull
topologies: a finite basis in the target supplies finitely many elements
whose fixing subgroup is an open neighborhood in the source.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open scoped Topology

variable {K L A B : Type*} [Field K] [Field L] [Field A] [Field B]
  [Algebra K A] [Algebra L B] [IsGalois L B]

/-- An equivariant field embedding makes its Galois group map continuous. -/
theorem galoisHom_continuous (i : A →+* B) (f : Gal(B/L) →* Gal(A/K))
    (heq : ∀ g x, i (f g x) = g (i x)) : Continuous f := by
  classical
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro V hV
  rw [map_one, krullTopology_mem_nhds_one_iff] at hV
  obtain ⟨F, hF, hFV⟩ := hV
  let := hF
  let b := Module.finBasis K F
  let S : Set B := Set.range (fun j => i (b j : A))
  let T := IntermediateField.adjoin L S
  let : Finite S := Set.finite_range _ |>.to_subtype
  let : FiniteDimensional L T := IntermediateField.finiteDimensional_adjoin
    (fun x _ => Algebra.IsIntegral.isIntegral x)
  apply Filter.mem_of_superset (T.fixingSubgroup_isOpen.mem_nhds T.fixingSubgroup.one_mem)
  intro g hg
  apply hFV
  change g ∈ T.fixingSubgroup at hg
  change f g ∈ F.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
  have he : (f g).toLinearMap.comp F.val.toLinearMap = F.val.toLinearMap := by
    apply b.ext
    intro j
    apply i.injective
    change i (f g (b j : A)) = i (b j : A)
    rw [heq]
    exact hg _ (IntermediateField.subset_adjoin L S ⟨j, rfl⟩)
  intro x hx
  exact LinearMap.congr_fun he ⟨x, hx⟩

end LocalClassFieldTheory
