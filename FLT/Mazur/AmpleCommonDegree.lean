/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TensorPowerGeneratorOpen
public import FLT.Mazur.TensorPowerReassociation

/-!
# A common positive degree for an ample section cover

A finite affine section cover can be raised to one positive degree. Raising
a section preserves its entire generator open, so both affineness and the
covering property survive.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback
variable {X : Scheme.{u}} {L : X.Modules}

/-- An ample line bundle has a finite affine section cover in one positive degree. -/
theorem AmpleLineBundle.common_degree_section_cover (hL : AmpleLineBundle L) :
    ∃ (ι : Type u) (_ : Finite ι) (N : ℕ) (_ : 0 < N)
      (s : ι → Γ(tensorPower L N, ⊤)),
      (∀ i, IsAffineOpen (sectionGeneratorOpen (tensorPower L N) (s i))) ∧
      (⨆ i, sectionGeneratorOpen (tensorPower L N) (s i)) = ⊤ := by
  classical
  obtain ⟨ι, hι, n, s, hn, haff, hcover⟩ := hL.finite_section_cover
  let := hι
  let := Fintype.ofFinite ι
  let N := ∏ i, n i
  have hN : 0 < N := Finset.prod_pos (fun i _ ↦ hn i)
  have hd (i : ι) : ∃ k : ℕ, 0 < k ∧ n i * k = N := by
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    refine ⟨k, ?_, hk.symm⟩
    by_contra hk'
    have hk0 : k = 0 := by omega
    simp only [hk0, mul_zero] at hk
    exact hN.ne' hk
  choose k hk he using hd
  let e (i : ι) : tensorPower (tensorPower L (n i)) (k i) ≅ tensorPower L N :=
    tensorPowerMulIso L (n i) (k i) ≪≫ eqToIso (congrArg (tensorPower L) (he i))
  let t (i : ι) : Γ(tensorPower L N, ⊤) :=
    (e i).hom.app ⊤ (tensorPowerSection (tensorPower L (n i)) ⊤ (s i) (k i))
  have hopen (i : ι) : sectionGeneratorOpen (tensorPower L N) (t i) =
      sectionGeneratorOpen (tensorPower L (n i)) (s i) := by
    exact (sectionGeneratorOpen_iso (e i) _).trans
      (tensorPowerSection_generatorOpen (hL.2.1.tensorPower (n i)) (s i) (hk i))
  exact ⟨ι, hι, N, hN, t, fun i ↦ (hopen i).symm ▸ haff i, (iSup_congr hopen).trans hcover⟩

end FLT.Mazur.FCurve
