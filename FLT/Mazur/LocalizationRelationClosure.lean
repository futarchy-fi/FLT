/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizationCoefficientContraction
public import FLT.Mazur.NoetherianRelationContraction

/-!
# Finite relation closure commutes with localization

The relation ideal produced over localized coefficients is exactly the
localization of the ambient relation ideal. Thus a double-open vertex need not
be assigned an independent quotient ideal.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.NoetherianRelationContraction

universe u v w z

variable {P₀ : Type u} [CommRing P₀] {P : Type v} [CommRing P]
  {L₀ : Type w} [CommRing L₀] {L : Type z} [CommRing L]
  [Algebra P₀ L₀] [Algebra P L]
  (M₀ : Submonoid P₀) (M : Submonoid P)
  [IsLocalization M₀ L₀] [IsLocalization M L]
  (c : P₀ →+* P) (d : L₀ →+* L)
  (hcomm : d.comp (algebraMap P₀ L₀) = (algebraMap P L).comp c)
  (hM : M₀.map c = M)

include hcomm hM in
/-- Finite coefficient closure is compatible with the literal localized ambient ideal. -/
theorem relations_localization (I : Ideal P) :
    relations d (I.map (algebraMap P L)) = (relations c I).map (algebraMap P L) := by
  unfold relations
  rw [LocalizationCoefficientContraction.comap_localized_ideal M₀ M c d hcomm hM,
    Ideal.map_map, hcomm, ← Ideal.map_map]

include hcomm hM in
/-- Localized relation closure remains finite even over a non-Noetherian original ring. -/
theorem relations_localization_fg [IsNoetherianRing P₀] (I : Ideal P) :
    (relations d (I.map (algebraMap P L))).FG := by
  rw [relations_localization M₀ M c d hcomm hM]
  exact (relations_fg c I).map (algebraMap P L)

end FLT.Mazur.NoetherianRelationContraction
