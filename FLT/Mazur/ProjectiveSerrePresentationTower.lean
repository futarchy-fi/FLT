/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveTwistQuotient

/-!
# Finite towers of coherent twist presentations

A tower retains the actual finite negative-twist quotients and their coherent
kernels. It contains no cohomology or vanishing assumptions. Keeping these
choices fixed is useful when seeking a uniform bound after base change.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- A finite sequence of coherent twist presentations, each presenting the previous kernel. -/
inductive TwistPresentationTower : (space R ι).Modules → ℕ → Type (u + 1)
  /-- A tower of length zero carries no presentation. -/
  | zero (F : (space R ι).Modules) : TwistPresentationTower F 0
  /-- One finite negative-twist presentation followed by a tower for its kernel. -/
  | step {F : (space R ι).Modules} {c : ℕ}
      (d : ℕ) (κ : Type u) (finite : Finite κ)
      (p : (∐ fun _ : κ ↦ twistingSheaf R ι (-(d : ℤ))) ⟶ F)
      (coherent : CoherentDevissage.CoherentSequence (ShortComplex.kernelSequence p))
      (tail : TwistPresentationTower (kernel p) c) : TwistPresentationTower F (c + 1)

/-- The maximum presentation degree is a single integer attached to the whole finite tower. -/
def TwistPresentationTower.bound {F : (space R ι).Modules} {c : ℕ}
    (T : TwistPresentationTower R ι F c) : ℕ :=
  match T with
  | .zero _ => 0
  | .step d _ _ _ _ tail => max d (TwistPresentationTower.bound tail)

variable [IsNoetherianRing R] [Finite ι]

/-- Every coherent coefficient admits a twist-presentation tower of any finite length. -/
theorem nonempty_twistPresentationTower (F : (space R ι).Modules)
    [F.IsFinitePresentation] (c : ℕ) : Nonempty (TwistPresentationTower R ι F c) := by
  induction c generalizing F with
  | zero => exact ⟨.zero F⟩
  | succ c ih =>
    obtain ⟨d, κ, hκ, p, hp⟩ := exists_coherent_twist_presentation R ι F
    let _kernelCoherent : (kernel p).IsFinitePresentation := hp.finite₁
    obtain ⟨tail⟩ := ih (kernel p)
    exact ⟨.step d κ hκ p hp tail⟩

/-- Choose the actual presentation data, without adding any geometric or vanishing input. -/
def coherentTwistPresentationTower (F : (space R ι).Modules)
    [F.IsFinitePresentation] (c : ℕ) : TwistPresentationTower R ι F c :=
  Classical.choice (nonempty_twistPresentationTower R ι F c)

end FLT.Mazur.ProjectiveSpace
