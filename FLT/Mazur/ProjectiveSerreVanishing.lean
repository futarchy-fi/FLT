/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistedPresentation

/-!
# Serre vanishing for coherent sheaves on polynomial projective space

Over a Noetherian ring, sufficiently positive twists of a coherent sheaf have
vanishing actual cohomology in all positive degrees, with a single bound.
This is absolute cohomology; relative higher direct images require a further
localization and sheafification argument.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.ProjectiveSpace

open LocalizationDegree

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u) [Finite ι]

/-- One twist bound kills every positive cohomology group of a coherent sheaf. -/
theorem exists_twistTensor_moduleH_subsingleton
    (F : (space R ι).Modules) [F.IsFinitePresentation] :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH (twistTensor R ι F (n : ℤ)) (q + 1)) := by
  let _index : Fintype ι := Fintype.ofFinite ι
  have h : ∀ k, ∀ (M : (space R ι).Modules) [M.IsFinitePresentation],
      ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ, Fintype.card ι ≤ q + 1 + k →
        Subsingleton (ModuleH (twistTensor R ι M (n : ℤ)) (q + 1)) := by
    intro k
    induction k with
    | zero =>
      intro M _
      refine ⟨0, fun n _ q hq ↦ ?_⟩
      exact finiteAffineCover_moduleH_subsingleton (twistTensor R ι M (n : ℤ))
        (chart R ι) (fun i ↦ Proj.isAffineOpen_basicOpen (grading R ι) (X i)
          (isHomogeneous_X R i) (by decide)) (iSup_chart R ι) (q + 1) (by omega)
    | succ k ih =>
      intro M _
      obtain ⟨d, κ, hκ, p, hp⟩ := exists_coherent_twist_presentation R ι M
      let _finite := hκ
      let _kernelCoherent : (kernel p).IsFinitePresentation := hp.finite₁
      obtain ⟨N, hN⟩ := ih (kernel p)
      refine ⟨max N d, fun n hn q hq ↦ ?_⟩
      let _kernelZero :
          Subsingleton (ModuleH (twistTensor R ι (kernel p) (n : ℤ)) (q + 1 + 1)) :=
        hN n (le_trans (le_max_left N d) hn) (q + 1) (by omega)
      let _sumZero : Subsingleton (ModuleH (twistTensor R ι
          (∐ fun _ : κ ↦ twistingSheaf R ι (-(d : ℤ))) (n : ℤ)) (q + 1)) :=
        twistTensor_twistSum_moduleH_subsingleton R ι (-(d : ℤ)) (n : ℤ) (by omega) q
      exact @moduleH_subsingleton_right (space R ι)
        ((ShortComplex.kernelSequence p).map (twistTensorFunctor R ι (n : ℤ)))
        (twistTensor_shortExact R ι _ hp.shortExact (n : ℤ)) (q + 1) _sumZero _kernelZero
  obtain ⟨N, hN⟩ := h (Fintype.card ι) F
  exact ⟨N, fun n hn q ↦ hN n hn q (by omega)⟩

end FLT.Mazur.ProjectiveSpace
