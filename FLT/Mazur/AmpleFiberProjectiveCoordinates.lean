/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleFiberGeneratorNeighborhood
public import FLT.Mazur.FiberAffineOpenBaseChange
public import FLT.Mazur.FiniteSectionCoverReindex

/-!
# Projective coordinates near an ample fiber

The lifted global numerators give an actual generating coordinate family
on a restricted proper family. Its opens on the chosen restricted fiber
remain affine, so it supplies the hypotheses for the finite-morphism step.
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

/-- An ample fiber supplies projective coordinates near it with affine fiber chart opens. -/
theorem exists_projective_coordinate_neighborhood (N : ℕ) :
    ∃ (V : S.Opens) (hsV : s ∈ V), IsAffineOpen V ∧
      ∃ (n : ℕ), N ≤ n ∧ 0 < n ∧ ∃ (d : ℕ)
        (t : Fin (d + 1) → Γ(tensorPower ((pullback (f ⁻¹ᵁ V).ι).obj L) n, ⊤)),
        (⨆ i, sectionGeneratorOpen
          (tensorPower ((pullback (f ⁻¹ᵁ V).ι).obj L) n) (t i)) = ⊤ ∧
        ∀ i, IsAffineOpen ((f ∣_ V).fiberι ⟨s, hsV⟩ ⁻¹ᵁ sectionGeneratorOpen
          (tensorPower ((pullback (f ⁻¹ᵁ V).ι).obj L) n) (t i)) := by
  obtain ⟨n, hn, hn0, ι, hι, a, V, hsV, hV, haff, hcover⟩ :=
    exists_global_generator_neighborhood f s hline hL N
  obtain ⟨d, b, hb, hbaff⟩ :=
    exists_fin_affine_section_family (tensorPower L n) (f.fiberι s) a haff
  let j := (f ⁻¹ᵁ V).ι
  let e := tensorPowerIso j L n
  let t (i : Fin (d + 1)) := e.hom.app ⊤ (pullGlobal j (tensorPower L n) (b i))
  have hopen (i : Fin (d + 1)) : sectionGeneratorOpen
      (tensorPower ((pullback j).obj L) n) (t i) =
        j ⁻¹ᵁ sectionGeneratorOpen (tensorPower L n) (b i) := by
    rw [sectionGeneratorOpen_iso, sectionGeneratorOpen_pullGlobal (hline.tensorPower n)]
  refine ⟨V, hsV, hV, n, hn, hn0, d, t, ?_, ?_⟩
  · apply top_unique
    intro x _
    have hx := hcover x.2
    rw [← hb] at hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    apply Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    rw [hopen]
    exact hi
  · intro i
    rw [hopen]
    exact Approximation.isAffineOpen_fiber_preimage_morphismRestrict f V ⟨s, hsV⟩
      (sectionGeneratorOpen (tensorPower L n) (b i)) (hbaff i)

end FLT.Mazur.StalkBase
