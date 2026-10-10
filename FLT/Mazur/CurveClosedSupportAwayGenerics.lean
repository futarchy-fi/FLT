/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedSubsets
public import FLT.Mazur.CurveGenericLineComparison

/-!
# Finite closed support away from all curve generic points

A closed subset of a Noetherian curve missing every component generic point
is finite. This treats reducible curves and supplies the finite-support error
criterion for comparisons which are isomorphisms at all generic points.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Set

namespace FLT.Mazur.FCurve

/-- A closed subset missing every component generic point of a curve is finite. -/
theorem finite_of_isClosed_disjoint_generics {T : Type*} [TopologicalSpace T]
    [NoetherianSpace T] [T0Space T] [QuasiSober T]
    (hd : topologicalKrullDim T ≤ 1) {Z : Set T} (hZ : IsClosed Z)
    (hg : Disjoint Z (genericPoints T)) : Z.Finite := by
  obtain ⟨S, hS, hc, hi, he⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [he]
  apply hS.sUnion
  intro C hC
  let D : IrreducibleCloseds T := ⟨C, hi C hC, hc C hC⟩
  have hCZ : C ⊆ Z := he ▸ subset_sUnion_of_mem hC
  have hmin : IsMin D := by
    rcases Order.krullDim_le_one_iff.mp hd D with hm | hm
    · exact hm
    · obtain ⟨W, hW, hCW⟩ :=
        exists_mem_irreducibleComponents_subset_of_isIrreducible C (hi C hC)
      let E : IrreducibleCloseds T :=
        ⟨W, hW.1, isClosed_of_mem_irreducibleComponents W hW⟩
      have hWC : W ⊆ C := hm (show D ≤ E from hCW)
      let η := genericPoints.ofComponent (⟨W, hW⟩ : irreducibleComponents T)
      exact (Set.disjoint_left.mp hg
        (hCZ (hWC (genericPoints.isGenericPoint_ofComponent ⟨W, hW⟩).mem)) η.property).elim
  obtain ⟨x, hx⟩ := eq_singleton_of_isMin_irreducibleCloseds D hmin
  change C = {x} at hx
  rw [hx]
  exact finite_singleton x

open CoherentDevissage

/-- Generic isomorphisms give finite-support cokernels without integrality. -/
theorem finite_cokernel_support_of_all_generic_isIso
    {X : Scheme} [IsNoetherian X] (hd : topologicalKrullDim X ≤ 1)
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsFinitePresentation]
    (a : M ⟶ N) (ha : ∀ x ∈ genericPoints X, IsIso ((stalk x).map a)) :
    (support (cokernel a)).Finite := by
  have := coherent_cokernel a
  apply finite_of_isClosed_disjoint_generics hd (isClosed_support _)
  apply Set.disjoint_left.mpr
  intro x hx hg
  have := ha x hg
  exact ((isIso_stalk_iff_notMem_support a x).mp inferInstance).2 hx

end FLT.Mazur.FCurve
