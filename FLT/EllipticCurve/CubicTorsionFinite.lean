/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTorsionGeometricFiber
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Finiteness of the actual multiplication kernel -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

/-- Finiteness of the underlying torsion fiber descends from an algebraic closure. -/
theorem finite_torsionModel_fieldFiber
    (K : Type u) [Field K] [Algebra R K] {n : ℕ} (hn : n ≠ 0) :
    Finite ↥(pullback (torsionModel W n).hom
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) := by
  let Ω := AlgebraicClosure K
  let : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  let f := (torsionModel W n).hom
  let g := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let j := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have hcomp : j ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    rw [← Spec.map_comp]
    rfl
  have : Finite ↥(pullback f (j ≫ g) : Scheme) := by
    rw [hcomp]
    exact finite_torsionModel_geometricFiber W Ω hn
  have : Finite ↥(pullback (pullback.snd f g) j : Scheme) :=
    Finite.of_equiv _ (pullbackLeftPullbackSndIso f g j).symm.hom.homeomorph.toEquiv
  have : Surjective j := ⟨fun x => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ x⟩⟩
  exact Finite.of_surjective (pullback.fst (pullback.snd f g) j)
    (Scheme.Hom.surjective _)

/-- Every nonzero multiplication kernel is locally quasi-finite over the base. -/
theorem torsionModel_locallyQuasiFinite {n : ℕ} (hn : n ≠ 0) :
    LocallyQuasiFinite (torsionModel W n).hom := by
  let f := (torsionModel W n).hom
  have : IsProper f := torsionModel_proper W n
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  intro x
  let K : Type u := IsLocalRing.ResidueField ((Spec (.of R)).presheaf.stalk x)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective ((Spec (.of R)).fromSpecResidueField x)
  let : Algebra R K := φ.hom.toAlgebra
  have : Finite ↥(f.fiber x) := by
    change Finite ↥(pullback f ((Spec (.of R)).fromSpecResidueField x) : Scheme)
    rw [← hφ]
    exact finite_torsionModel_fieldFiber W K hn
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (f.fiberHomeo x).toEquiv)

/-- The represented nonzero-order torsion scheme is finite over its coefficient ring. -/
theorem torsionModel_finite {n : ℕ} (hn : n ≠ 0) :
    IsFinite (torsionModel W n).hom := by
  have := torsionModel_proper W n
  have := torsionModel_locallyQuasiFinite W hn
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end WeierstrassCurve.CubicCharts
