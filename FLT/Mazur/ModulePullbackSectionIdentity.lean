/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorLineSectionModel

/-!
# Sealed identities for pullback of section maps

The predicate is the actual commuting section square. Sealing it avoids
expanding concrete dual sheaves when specializing generic divisor identities.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The specified pullback comparison carries one actual section map to the other. -/
irreducible_def PullbackPreservesSection {L : Y.Modules} {M : X.Modules}
    (e : (pullback f).obj L ≅ M) (s : structureModule Y ⟶ L)
    (t : structureModule X ⟶ M) : Prop :=
  (pullback f).map s ≫ e.hom = (modulePullbackUnitIso f).hom ≫ t

/-- Unsealing recovers exactly the original commuting square of section maps. -/
theorem pullbackPreservesSection_iff {L : Y.Modules} {M : X.Modules}
    (e : (pullback f).obj L ≅ M) (s : structureModule Y ⟶ L)
    (t : structureModule X ⟶ M) :
    PullbackPreservesSection f e s t ↔
      (pullback f).map s ≫ e.hom = (modulePullbackUnitIso f).hom ≫ t := by
  rw [PullbackPreservesSection_def]

/-- The canonical divisor comparison preserves the actual modeled divisor sections. -/
theorem divisorLineModel_preservesSection {I : Y.IdealSheafData} {J : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (h : I.comap f = J)
    [IsIso (idealModulePullbackHom I f)] :
    PullbackPreservesSection f (divisorLineModelPullbackIso f hI hJ h)
      (divisorLineModelSection hI) (divisorLineModelSection hJ) := by
  rw [pullbackPreservesSection_iff]
  exact divisorLineModelPullbackIso_section f hI hJ h

end FLT.Mazur.FCurve
