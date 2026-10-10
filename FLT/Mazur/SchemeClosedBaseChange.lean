/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeBaseChangeLimit
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Closed inverse systems after base change

Base change retains closed transition maps and closed limit projections.
Quasi-separatedness of the fixed scheme then supplies it at every stage.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {I : Type v} [Category I] {S Y : Scheme.{u}}
  {D : I ⥤ Scheme.{u}} (t : D ⟶ (Functor.const I).obj S) (q : Y ⟶ S)

/-- Closed transitions remain closed under the fixed base change. -/
instance schemeBaseChangeDiagram_map_isClosedImmersion
    [∀ {i j} (f : i ⟶ j), IsClosedImmersion (D.map f)]
    {i j : I} (f : i ⟶ j) : IsClosedImmersion ((schemeBaseChangeDiagram t q).map f) :=
  MorphismProperty.of_isPullback (schemeBaseChangeDiagram_isPullback t q f).flip
    (inferInstanceAs (IsClosedImmersion (D.map f)))

/-- Closed limit projections stay closed after base change. -/
theorem schemeBaseChangeCone_app_isClosedImmersion (c : Cone D)
    (b : c.pt ⟶ S) (hb : ∀ i, c.π.app i ≫ t.app i = b)
    (i : I) [IsClosedImmersion (c.π.app i)] :
    IsClosedImmersion ((schemeBaseChangeCone t q c b hb).π.app i) :=
  MorphismProperty.of_isPullback (schemeBaseChangeCone_isPullback t q c b hb i).flip
    (inferInstanceAs (IsClosedImmersion (c.π.app i)))

/-- Closed maps to the fixed base preserve quasi-separatedness of the pulled-back scheme. -/
theorem schemeBaseChangeDiagram_quasiSeparatedSpace [QuasiSeparatedSpace Y]
    [∀ i, IsClosedImmersion (t.app i)] (i : I) :
    QuasiSeparatedSpace ((schemeBaseChangeDiagram t q).obj i) := by
  let r : D.obj i ⟶ S := t.app i
  let _ : IsClosedImmersion r := inferInstanceAs (IsClosedImmersion (t.app i))
  exact quasiSeparatedSpace_of_quasiSeparated (X := pullback q r) (pullback.fst q r)

end FLT.Mazur.Approximation
