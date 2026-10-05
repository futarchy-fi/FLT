/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoherentRingCohomologyFinite
public import FLT.Mazur.AcyclicPushforwardCohomology
public import FLT.Mazur.ProjectiveCoherentCohomology

/-!
# Finite base-ring cohomology under geometric comparison

Acyclic and closed direct images retain all-degree finiteness for the
specified base-ring action. A closed projective presentation supplies it
unconditionally for coherent coefficients over a Noetherian ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.FCurve

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]

/-- All-degree finite cohomology transfers along an actual acyclic direct image. -/
theorem acyclicPushforward_hasFiniteRingCohomology_iff (f : X ⟶ Y)
    (M : X.Modules) (hM : ModulePushforwardAcyclic f M) (ρ : R →+* Γ(Y, ⊤)) :
    HasFiniteRingCohomology ρ ((pushforward f).obj M) ↔
      HasFiniteRingCohomology (f.appTop.hom.comp ρ) M :=
  forall_congr' fun n ↦ acyclicPushforward_moduleRingH_finite_iff f M hM ρ n

/-- Closed direct image retains finiteness with the induced base-ring action. -/
theorem closedPushforward_hasFiniteRingCohomology_iff [Y.IsSeparated]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (M : X.Modules) [M.IsFinitePresentation] (ρ : R →+* Γ(Y, ⊤)) :
    HasFiniteRingCohomology ρ ((pushforward f).obj M) ↔
      HasFiniteRingCohomology (f.appTop.hom.comp ρ) M :=
  forall_congr' fun n ↦ closedPushforward_moduleH_finite_iff f M ρ n

/-- A closed projective presentation supplies all-degree finite base-ring cohomology. -/
theorem projective_hasFiniteRingCohomology [IsNoetherianRing R]
    {ι : Type u} [Finite ι] (f : X ⟶ ProjectiveSpace.space R ι) [IsClosedImmersion f]
    (M : X.Modules) [M.IsFinitePresentation] :
    HasFiniteRingCohomology
      (f.appTop.hom.comp (ProjectiveSpace.LocalizationDegree.constantSection R ι ⊤)) M :=
  fun n ↦ ProjectiveSpace.closedSubscheme_coherent_moduleH_finite R ι f M n

end FLT.Mazur.FCurve
