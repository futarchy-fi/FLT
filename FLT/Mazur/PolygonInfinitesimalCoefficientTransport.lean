/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalMarkedBaseChange

/-!
# Coefficient maps with a specified target parameter

Apply the complete family comparison to an explicit ring map and an equality
of actual smoothing parameters. This transports the construction to concrete
truncated coefficient stages without replacing their chosen parameters.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.PolygonInfinitesimal

variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t : R) (s : S) [Fact (IsNilpotent t)] [Fact (IsNilpotent s)]
  (hs : f t = s) (n : ℕ) (h : 2 ≤ n)

/-- The assembled coefficient projection with the specified target parameter. -/
def parameterProjection : scheme S s n h ⟶ scheme R t n h := by
  let _ := f.toAlgebra
  subst s
  exact coefficientProjection R S t n h

/-- The concrete-parameter coefficient square is cartesian. -/
theorem parameterProjection_isPullback :
    IsPullback (parameterProjection f t s hs n h) (toBase S s n h)
      (toBase R t n h) (Spec.map (CommRingCat.ofHom f)) := by
  subst s
  let _ := f.toAlgebra
  exact coefficientProjection_isPullback R S t n h

/-- The concrete-parameter coefficient projection retains the arithmetic base. -/
@[reassoc] theorem parameterProjection_base :
    parameterProjection f t s hs n h ≫ toBase R t n h =
      toBase S s n h ≫ Spec.map (CommRingCat.ofHom f) :=
  (parameterProjection_isPullback f t s hs n h).w

/-- The pullback isomorphism for the chosen ring map and actual target parameter. -/
def parameterPullbackIso : scheme S s n h ≅
    pullback (toBase R t n h) (Spec.map (CommRingCat.ofHom f)) :=
  (parameterProjection_isPullback f t s hs n h).isoPullback

/-- The comparison retains the coefficient projection to the original family. -/
@[reassoc] theorem parameterPullbackIso_fst :
    (parameterPullbackIso f t s hs n h).hom ≫ pullback.fst _ _ =
      parameterProjection f t s hs n h :=
  (parameterProjection_isPullback f t s hs n h).isoPullback_hom_fst

/-- The comparison retains the chosen target base. -/
@[reassoc] theorem parameterPullbackIso_snd :
    (parameterPullbackIso f t s hs n h).hom ≫ pullback.snd _ _ = toBase S s n h :=
  (parameterProjection_isPullback f t s hs n h).isoPullback_hom_snd

/-- All original unit markings are retained under the concrete parameter projection. -/
@[reassoc] theorem marking_parameterProjection (i : Fin n) (a : Rˣ) :
    marking S s n h i (Units.map f a) ≫ parameterProjection f t s hs n h =
      Spec.map (CommRingCat.ofHom f) ≫ marking R t n h i a := by
  subst s
  let _ := f.toAlgebra
  exact marking_coefficientProjection R S t n h i a

/-- The comparison retains the entire pulled-back marking for a chosen target parameter. -/
theorem marking_parameterPullbackIso (i : Fin n) (a : Rˣ) :
    marking S s n h i (Units.map f a) ≫ (parameterPullbackIso f t s hs n h).hom =
      pullback.lift (Spec.map (CommRingCat.ofHom f) ≫ marking R t n h i a) (𝟙 _)
        (by rw [Category.assoc, marking_base, Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, parameterPullbackIso_fst, pullback.lift_fst,
      marking_parameterProjection]
  · rw [Category.assoc, parameterPullbackIso_snd, pullback.lift_snd, marking_base]

end FLT.Mazur.PolygonInfinitesimal
