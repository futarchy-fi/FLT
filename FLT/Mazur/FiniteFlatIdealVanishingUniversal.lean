/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatIdealVanishingNaturality
public import FLT.Mazur.FiniteFlatIdealVanishingZero

/-!
# The global universal property of finite flat ideal vanishing

A map factors through the closed coefficient locus precisely when the actual
pulled ideal vanishes on the whole cartesian family. The factorization is
unique, and the universal family over the locus kills the original ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.FiniteFlatIdealVanishing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {D E S T : Scheme} {g : D ⟶ S} {q : E ⟶ T} {i : E ⟶ D} {f : T ⟶ S}
  [IsFinite g] [Flat g] [LocallyOfFinitePresentation g]
  [IsFinite q] [Flat q] [LocallyOfFinitePresentation q]
  (H : IsPullback i q g f) (J : D.IdealSheafData)

include H in
/-- The global closed locus represents vanishing of the full ideal on any base change. -/
theorem locus_factorization_iff :
    (∃ k : T ⟶ locus g J, k ≫ locusInclusion g J = f) ↔ J.comap i = ⊥ := by
  rw [← idealSheaf_eq_bot_iff q (J.comap i), idealSheaf_baseChange H J]
  have hc : (idealSheaf g J).comap f = ⊥ ↔ idealSheaf g J ≤ f.ker := by
    rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le,
      Scheme.IdealSheafData.map_bot]
  rw [hc]
  constructor
  · rintro ⟨k, rfl⟩
    simpa only [locusInclusion, Scheme.IdealSheafData.ker_subschemeι] using
      Scheme.Hom.le_ker_comp k (locusInclusion g J)
  · intro h
    have hk : (locusInclusion g J).ker ≤ f.ker := by
      simpa only [locusInclusion, Scheme.IdealSheafData.ker_subschemeι] using h
    exact ⟨IsClosedImmersion.lift (locusInclusion g J) f hk,
      IsClosedImmersion.lift_fac _ _ _⟩

/-- The unique factorization of a parameter that kills the actual pulled ideal. -/
def locusLift (h : J.comap i = ⊥) : T ⟶ locus g J :=
  ((locus_factorization_iff H J).mpr h).choose

/-- The factorization recovers the exact original parameter map. -/
@[reassoc (attr := simp)] theorem locusLift_inclusion (h : J.comap i = ⊥) :
    locusLift H J h ≫ locusInclusion g J = f :=
  ((locus_factorization_iff H J).mpr h).choose_spec

/-- The global closed immersion makes every factorization unique. -/
theorem locusLift_unique (h : J.comap i = ⊥) (k : T ⟶ locus g J)
    (hk : k ≫ locusInclusion g J = f) : k = locusLift H J h := by
  apply (cancel_mono (locusInclusion g J)).mp
  rw [hk, locusLift_inclusion]

/-- The entire universal cartesian family over the locus kills the original ideal. -/
theorem universalIdeal_eq_bot :
    J.comap (pullback.snd (locusInclusion g J) g) = ⊥ := by
  apply (locus_factorization_iff (IsPullback.of_hasPullback (locusInclusion g J) g).flip J).mp
  exact ⟨𝟙 _, Category.id_comp _⟩

end FLT.Mazur.FiniteFlatIdealVanishing
