/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicCohomologyScalars
public import FLT.Mazur.BaseAdicThickening
public import FLT.Mazur.ProperRingCohomologyFinite

/-!
# The actual cohomology filtration over an affine base

The scheme structure map supplies the scalar compatibility for an extended
base ideal. Properness supplies finite cohomology and finite image modules.
No adic completeness or stability of the image filtration is presumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.FCurve FLT.Mazur.Chow.AffineBase
open FLT.Mazur.BaseAdicThickening FLT.Mazur.IdealAdicQuotient

namespace FLT.Mazur.BaseAdicCohomology

variable {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R) (J : Ideal R)

/-- A base ideal scalar lies in the extended ideal on every affine source open. -/
lemma scalar_mem (r : R) (hr : r ∈ J) (U : X.affineOpens) :
    X.presheaf.map U.1.leTop.op (baseCohomologyScalars f r) ∈
      ((baseIdeal R J).comap f).ideal U := by
  have h := extendedPower_ideal J f U 1
  simp only [pow_one] at h
  rw [h]
  have he : X.presheaf.map U.1.leTop.op (baseCohomologyScalars f r) =
      (f.appLE ⊤ U.1 (by simp)) ((Scheme.ΓSpecIso R).inv r) := by
    rfl
  rw [he]
  exact Ideal.mem_map_of_mem _ hr

variable [IsNoetherianRing R] [IsProper f]

/-- The cohomology images for the extended base ideal form an actual ideal filtration. -/
def imageFiltration (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    J.Filtration (ModuleRingH (baseCohomologyScalars f) M q) := by
  let _ := Chow.source_isNoetherian f
  exact cohomologyFiltration (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (scalar_mem f J) q

/-- The filtration terms are the images of the original ideal-power inclusions. -/
lemma imageFiltration_N (M : X.Modules) [M.IsFinitePresentation] (q n : ℕ) :
    let _ := Chow.source_isNoetherian f
    (imageFiltration f J M q).N n =
      cohomologyImage (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q n := rfl

/-- Every image term is finite over the Noetherian base ring. -/
theorem imageFiltration_finite (M : X.Modules) [M.IsFinitePresentation] (q n : ℕ) :
    Module.Finite R ((imageFiltration f J M q).N n) := by
  let _ := proper_coherent_hasFiniteRingCohomology f M q
  infer_instance

/-- The base-adic filtration is contained in the geometric cohomology image filtration. -/
lemma adic_le_imageFiltration (M : X.Modules) [M.IsFinitePresentation] (q n : ℕ) :
    J ^ n • (⊤ : Submodule R (ModuleRingH (baseCohomologyScalars f) M q)) ≤
      (imageFiltration f J M q).N n := by
  let _ := Chow.source_isNoetherian f
  exact idealPower_smul_top_le_cohomologyImage (baseCohomologyScalars f)
    ((baseIdeal R J).comap f) M J (scalar_mem f J) q n

end FLT.Mazur.BaseAdicCohomology
