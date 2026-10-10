/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleFiberGlobalGenerators
public import FLT.Mazur.ProperFiberNeighborhood

/-!
# Finite generators near an ample fiber

Global numerators generate over an affine neighborhood of the chosen base
point. Their actual pullbacks generate the corresponding power of the
restricted line bundle on the entire restricted family.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules FLT.Mazur.FCurve ModuleLineBundleTensorPullback

namespace FLT.Mazur.StalkBase

variable {X S : Scheme.{0}} [IsAffine S] [IsLocallyNoetherian S]
  [CompactSpace X] [X.IsSeparated] (f : X ⟶ S) [IsProper f] (s : S)
  {L : X.Modules} (hline : LocallyFreeRankOne L)
  (hL : AmpleLineBundle ((pullback (f.fiberι s)).obj L))

include hline hL

/-- A high-power section cover of an ample fiber spreads to an affine base neighborhood. -/
theorem exists_global_generator_neighborhood (N : ℕ) :
    ∃ (n : ℕ), N ≤ n ∧ 0 < n ∧ ∃ (ι : Type) (_ : Finite ι)
      (a : ι → Γ(tensorPower L n, ⊤)) (V : S.Opens),
      s ∈ V ∧ IsAffineOpen V ∧
      (∀ i, IsAffineOpen (f.fiberι s ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) (a i))) ∧
      f ⁻¹ᵁ V ≤ ⨆ i, sectionGeneratorOpen (tensorPower L n) (a i) := by
  obtain ⟨n, hn, hn0, ι, hι, a, haff, hcover⟩ := exists_global_fiber_cover f s hline hL N
  obtain ⟨W, hsW, hW⟩ := Approximation.exists_proper_fiber_cover_neighborhood f s
    (fun i ↦ sectionGeneratorOpen (tensorPower L n) (a i)) hcover
  obtain ⟨V, hV, hsV, hVW⟩ := exists_isAffineOpen_mem_and_subset hsW
  exact ⟨n, hn, hn0, ι, hι, a, V, hsV, hV, haff,
    (fun _ hx ↦ hW (hVW hx))⟩

/-- The restricted line has an actual finite generating family in arbitrarily high degree. -/
theorem exists_restricted_generator_cover (N : ℕ) :
    ∃ (V : S.Opens), s ∈ V ∧ IsAffineOpen V ∧
      ∃ (n : ℕ), N ≤ n ∧ 0 < n ∧ ∃ (ι : Type) (_ : Finite ι)
        (t : ι → Γ(tensorPower ((pullback (f ⁻¹ᵁ V).ι).obj L) n, ⊤)),
        (⨆ i, sectionGeneratorOpen
          (tensorPower ((pullback (f ⁻¹ᵁ V).ι).obj L) n) (t i)) = ⊤ := by
  obtain ⟨n, hn, hn0, ι, hι, a, V, hsV, hV, _, hcover⟩ :=
    exists_global_generator_neighborhood f s hline hL N
  let j := (f ⁻¹ᵁ V).ι
  let e := tensorPowerIso j L n
  let t (i : ι) := e.hom.app ⊤ (pullGlobal j (tensorPower L n) (a i))
  refine ⟨V, hsV, hV, n, hn, hn0, ι, hι, t, ?_⟩
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover x.2)
  apply Opens.mem_iSup.mpr
  refine ⟨i, ?_⟩
  change x ∈ sectionGeneratorOpen _ (e.hom.app ⊤ _)
  rw [sectionGeneratorOpen_iso, sectionGeneratorOpen_pullGlobal (hline.tensorPower n)]
  exact hi

end FLT.Mazur.StalkBase
