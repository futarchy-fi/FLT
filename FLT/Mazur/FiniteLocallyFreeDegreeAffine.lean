/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocallyFreeDegreeCover

/-!
# Algebraic consequences of finite locally free degree

Cartesian squares transfer the full degree contract. For actual algebra
spectra the contract gives finite presentation as a module, flatness and
constant residue-field dimension, without assuming these properties first.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false

/-- Every specified cartesian square preserves finite locally free degree. -/
theorem finiteLocallyFreeDegree_of_isPullback {W X Y Z : Scheme.{u}}
    {a : W ⟶ X} {b : W ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (d : ℕ) (hf : FiniteLocallyFreeDegree f d) :
    FiniteLocallyFreeDegree b d := by
  let e : Over.mk b ≅ Over.mk (pullback.snd f g) :=
    Over.isoMk h.isoPullback h.isoPullback_hom_snd
  exact (finiteLocallyFreeDegree_iff_of_overIso e).mpr (hf.baseChange g)

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (d : ℕ)
variable (h : FiniteLocallyFreeDegree (Spec.map (CommRingCat.ofHom (algebraMap R A))) d)
include h

/-- Finite degree of an algebra spectrum gives a finite underlying module. -/
theorem finiteLocallyFreeDegree_moduleFinite : Module.Finite R A :=
  RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp h.1)

/-- Flatness of the algebra spectrum gives flatness of its underlying module. -/
theorem finiteLocallyFreeDegree_moduleFlat : Module.Flat R A :=
  RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h.2.1)

/-- Scheme finite presentation and finiteness give module finite presentation. -/
theorem finiteLocallyFreeDegree_moduleFinitePresentation : Module.FinitePresentation R A := by
  let _ := finiteLocallyFreeDegree_moduleFinite R A d h
  let _ := RingHom.finitePresentation_algebraMap.mp
    ((LocallyOfFinitePresentation.SpecMap_iff _).mp h.2.2.1)
  exact Module.FinitePresentation.of_finite_of_finitePresentation R A

/-- The actual algebra has the prescribed dimension in every residue field. -/
theorem finiteLocallyFreeDegree_residueFinrank (p : PrimeSpectrum R) :
    Module.finrank p.asIdeal.ResidueField (p.asIdeal.Fiber A) = d := by
  let _ := finiteLocallyFreeDegree_moduleFinite R A d h
  let _ := finiteLocallyFreeDegree_moduleFlat R A d h
  rw [← Module.rankAtStalk_eq, ← Scheme.Hom.finrank_SpecMap_algebraMap]
  exact h.2.2.2 p

end FLT.Mazur.FCurve
