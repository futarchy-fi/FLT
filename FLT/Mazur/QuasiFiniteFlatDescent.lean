/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness descends for an original separated quasi-finite morphism

A finite entire cartesian pullback supplies universal closedness by flat
quasi-compact descent. The original separated quasi-finite morphism is then
proper and finite. No statement about finiteness of point fibers is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
variable {P D B A : Scheme.{u}} {a : P ⟶ D} {b : P ⟶ B} {p : D ⟶ A} {g : B ⟶ A}
  (H : IsPullback a b p g) [IsSeparated p] [LocallyQuasiFinite p]
  [LocallyOfFiniteType p] [Surjective g] [Flat g] [QuasiCompact g]

include H in
/-- A finite whole pullback detects finiteness of the original separated quasi-finite map. -/
theorem finite_of_flat_surjective_pullback [IsFinite b] : IsFinite p := by
  let _ : UniversallyClosed p :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      H.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  let _ : IsProper p := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite p

end FLT.Mazur.SchemeOpenEnvelope
