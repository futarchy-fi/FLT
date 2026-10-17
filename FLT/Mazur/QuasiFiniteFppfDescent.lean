/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiFiniteFlatDescent

/-!
# Finiteness descends along locally finitely presented flat covers

A finite entire cartesian pullback supplies universal closedness by flat
locally finitely presented descent. The original separated quasi-finite morphism is then
proper and finite. No statement about finiteness of point fibers is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P D B A : Scheme} {a : P ⟶ D} {b : P ⟶ B} {p : D ⟶ A} {g : B ⟶ A}
  (H : IsPullback a b p g) [IsSeparated p] [LocallyQuasiFinite p]
  [LocallyOfFiniteType p] [Surjective g] [Flat g] [LocallyOfFinitePresentation g]

include H in
/-- A finite whole pullback detects finiteness of the original separated quasi-finite map. -/
theorem finite_of_fppf_surjective_pullback [IsFinite b] : IsFinite p := by
  let _ : UniversallyClosed p :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
      H.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  let _ : IsProper p := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite p

end FLT.Mazur.SchemeOpenEnvelope
