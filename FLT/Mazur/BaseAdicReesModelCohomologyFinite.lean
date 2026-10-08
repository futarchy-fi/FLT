/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelDescent
public import FLT.Mazur.ProperRingCohomologyFinite

/-!
# Finite cohomology of the actual global Rees model

For a proper family over a Noetherian ring, the relative Rees space is
proper over the Rees spectrum. The globally descended original model
therefore has finite cohomology over the actual base Rees ring.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.Chow.AffineBase

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} (f : X ⟶ Spec R) [IsProper f] (J : Ideal R)

/-- The original relative Rees space maps to the actual base Rees spectrum. -/
def modelStructureMap : relativeSpace f J ⟶ Spec (.of (reesAlgebra J)) :=
  pullback.snd f (baseMap J)

/-- Properness persists under the actual Rees base change. -/
instance modelStructureMap_isProper : IsProper (modelStructureMap f J) := by
  unfold modelStructureMap
  infer_instance

/-- The base Rees structural action on the actual relative space. -/
def modelCohomologyScalars : reesAlgebra J →+* Γ(relativeSpace f J, ⊤) :=
  baseCohomologyScalars (modelStructureMap f J)

variable [IsLocallyNoetherian X] (M : X.Modules) [M.IsFinitePresentation]

/-- Proper coherent finiteness applies to the descended original model in every degree. -/
theorem globalModelSheaf_finite_cohomology (q : ℕ) :
    Module.Finite (reesAlgebra J)
      (ModuleRingH (modelCohomologyScalars f J) (globalModelSheaf f J M) q) :=
  proper_coherent_hasFiniteRingCohomology (modelStructureMap f J)
    (globalModelSheaf f J M) q

end FLT.Mazur.BaseAdicRees
