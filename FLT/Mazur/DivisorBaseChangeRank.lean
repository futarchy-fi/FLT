/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCartier
public import FLT.Mazur.ConstantDegree

/-!
# Rank of the actual pulled-back divisor scheme

The closed subscheme of the pulled-back ideal is isomorphic over the new base to
the pullback of the original closed subscheme. Thus its finite-flat rank is the
original rank composed with the base map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (I : X.IdealSheafData)

/-- The actual closed scheme defined by the pulled-back ideal remains finite. -/
theorem isFinite_divisor_baseChange [IsFinite (I.subschemeι ≫ f)] :
    IsFinite ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g) := by
  rw [← divisorBaseChangeIso_hom_snd]
  infer_instance

/-- Rank is preserved by the actual ideal-sheaf base-change construction. -/
theorem finrank_divisor_baseChange [IsFinite (I.subschemeι ≫ f)]
    [Flat (I.subschemeι ≫ f)] (t : T) :
    ((I.comap (pullback.fst f g)).subschemeι ≫ pullback.snd f g).finrank t =
      (I.subschemeι ≫ f).finrank (g t) := by
  rw [← divisorBaseChangeIso_hom_snd, Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_pullback_snd]

end FLT.Mazur.FCurve
