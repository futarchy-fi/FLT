/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalCoefficientDiagram

/-!
# Base change of the assembled infinitesimal polygon family

The complete coefficient transformation glues to the actual family projection.
Its square is cartesian. The resulting pullback isomorphism retains the original
chart projection and the arithmetic structure morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

open PolygonSmoothing

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (t : R) [Fact (IsNilpotent t)] [Fact (IsNilpotent (algebraMap R S t))]
  (n : ℕ) (h : 2 ≤ n)

/-- Coefficient projection of the actual assembled cyclic family. -/
def coefficientProjection : scheme S (algebraMap R S t) n h ⟶ scheme R t n h :=
  letI : Fact (2 ≤ n) := ⟨h⟩
  colimMap (coefficientDiagram R S t n)

/-- The glued projection retains the original map on every node chart. -/
@[reassoc] theorem chart_coefficientProjection (i : Fin n) :
    chart S (algebraMap R S t) n h i ≫ coefficientProjection R S t n h =
      chartCoefficient R S t ≫ chart R t n h i := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact ι_colimMap (coefficientDiagram R S t n) (.right i)

/-- The assembled coefficient square is a pullback, with every overlap retained. -/
theorem coefficientProjection_isPullback :
    IsPullback (coefficientProjection R S t n h) (toBase S (algebraMap R S t) n h)
      (toBase R t n h) (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let : Fact (2 ≤ n) := ⟨h⟩
  exact Approximation.equifibered_colimit_baseChange (coefficientDiagram R S t n)
    (coefficientDiagram_equifibered R S t n) (baseCocone S (algebraMap R S t) n)
    (baseCocone R t n) _ (coefficientDiagram_base R S t n)

/-- The glued projection preserves the specified arithmetic structure maps. -/
@[reassoc] theorem coefficientProjection_base :
    coefficientProjection R S t n h ≫ toBase R t n h =
      toBase S (algebraMap R S t) n h ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  (coefficientProjection_isPullback R S t n h).w

/-- The actual assembled family over the new coefficients is the original pullback. -/
def baseChangeIso : scheme S (algebraMap R S t) n h ≅
    pullback (toBase R t n h) (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (coefficientProjection_isPullback R S t n h).isoPullback

/-- The comparison retains the coefficient projection to the original family. -/
@[reassoc] theorem baseChangeIso_fst :
    (baseChangeIso R S t n h).hom ≫ pullback.fst _ _ = coefficientProjection R S t n h :=
  (coefficientProjection_isPullback R S t n h).isoPullback_hom_fst

/-- The comparison retains the original arithmetic base projection. -/
@[reassoc] theorem baseChangeIso_snd :
    (baseChangeIso R S t n h).hom ≫ pullback.snd _ _ =
      toBase S (algebraMap R S t) n h :=
  (coefficientProjection_isPullback R S t n h).isoPullback_hom_snd

/-- The pullback comparison preserves each complete chart's coefficient projection. -/
@[reassoc] theorem chart_baseChangeIso_fst (i : Fin n) :
    chart S (algebraMap R S t) n h i ≫ (baseChangeIso R S t n h).hom ≫
      pullback.fst _ _ = chartCoefficient R S t ≫ chart R t n h i := by
  rw [baseChangeIso_fst, chart_coefficientProjection]

/-- The pullback comparison preserves each complete chart's base projection. -/
@[reassoc] theorem chart_baseChangeIso_snd (i : Fin n) :
    chart S (algebraMap R S t) n h i ≫ (baseChangeIso R S t n h).hom ≫
      pullback.snd _ _ = chartStructure S (algebraMap R S t) := by
  rw [baseChangeIso_snd, chart_toBase]

/-- The assembled pullback comparison as an isomorphism of arithmetic families. -/
def familyBaseChangeIso : family S (algebraMap R S t) n h ≅
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj (family R t n h) :=
  Over.isoMk (baseChangeIso R S t n h) (baseChangeIso_snd R S t n h)

end FLT.Mazur.PolygonInfinitesimal
