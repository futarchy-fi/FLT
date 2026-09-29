/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveTwistCohomology
public import FLT.Mazur.ProjectiveTwistQuotient
public import FLT.Mazur.ModuleCohomologyRing
public import FLT.Mazur.FiniteAffineCoverDimension
public import FLT.Mazur.ClosedSubschemeCohomology

/-! # Finiteness of coherent cohomology on polynomial projective space -/

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

/-- Actual cohomology of every coherent sheaf on polynomial projective space
is finite over its Noetherian base, in every degree. -/
theorem coherent_moduleH_finite (F : (space R ι).Modules) [F.IsFinitePresentation] (n : ℕ) :
    letI := Module.compHom (ModuleH F n) (constantSection R ι ⊤)
    Module.Finite R (ModuleH F n) := by
  let _index : Fintype ι := Fintype.ofFinite ι
  let ρ := constantSection R ι ⊤
  have h : ∀ k q, Fintype.card ι ≤ q + k →
      ∀ (M : (space R ι).Modules) [M.IsFinitePresentation],
        Module.Finite R ((moduleRingHFunctor ρ q).obj M) := by
    intro k
    induction k with
    | zero =>
      intro q hq M _
      let _zero : Subsingleton ((moduleRingHFunctor ρ q).obj M) :=
        finiteAffineCover_moduleH_subsingleton M (chart R ι)
          (fun i ↦ Proj.isAffineOpen_basicOpen (grading R ι) (X i)
            (isHomogeneous_X R i) (by decide)) (iSup_chart R ι) q (by simpa using hq)
      infer_instance
    | succ k ih =>
      intro q hq M _
      obtain ⟨d, κ, hκ, p, hp⟩ := exists_coherent_twist_presentation R ι M
      let _finiteIndex := hκ
      let _kernelCoherent : (kernel p).IsFinitePresentation := hp.finite₁
      let _kernelFinite :
          Module.Finite R ((moduleRingHFunctor ρ (q + 1)).obj (kernel p)) :=
        ih (q + 1) (by omega) (kernel p)
      let _summandFinite :
          Module.Finite R ((moduleRingHFunctor ρ q).obj
            (twistingSheaf R ι (-(d : ℤ)))) :=
        twist_moduleH_finite R ι (-(d : ℤ)) q
      let _sumFinite :
          Module.Finite R ((moduleRingHFunctor ρ q).obj
            (∐ fun _ : κ ↦ twistingSheaf R ι (-(d : ℤ)))) :=
        moduleRingH_finite_coproduct ρ (fun _ : κ ↦ twistingSheaf R ι (-(d : ℤ))) q
      exact @moduleRingH_finite_right (space R ι) R _ ρ _
        (ShortComplex.kernelSequence p) hp.shortExact q _sumFinite _kernelFinite
  exact h (Fintype.card ι) n (by omega) F

/-- A specified projective embedding transfers coherent cohomology finiteness
to the embedded scheme, with the induced base-ring action. -/
theorem closedSubscheme_coherent_moduleH_finite {Y : Scheme.{u}}
    (f : Y ⟶ space R ι) [IsClosedImmersion f]
    (F : Y.Modules) [F.IsFinitePresentation] (n : ℕ) :
    letI := Module.compHom (ModuleH F n) (f.appTop.hom.comp (constantSection R ι ⊤))
    Module.Finite R (ModuleH F n) := by
  let _coherent : ((Scheme.Modules.pushforward f).obj F).IsFinitePresentation :=
    CoherentDevissage.closedPushforward_isFinitePresentation f F
  exact (closedPushforward_moduleH_finite_iff f F (constantSection R ι ⊤) n).mp
    (coherent_moduleH_finite R ι ((Scheme.Modules.pushforward f).obj F) n)

end FLT.Mazur.ProjectiveSpace
