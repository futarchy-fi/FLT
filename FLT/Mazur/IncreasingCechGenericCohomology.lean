/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechProperFinite
public import FLT.Mazur.FiniteCohomologyFreeNeighborhood

/-!
# A common generic projective locus for actual bounded Cech cohomology

Over a Noetherian domain all cohomology modules of the actual bounded complex
become projective after inverting one nonzero scalar. The cardinal bound
reduces all degrees to a finite collection. This is the input for a bounded
complex base-change argument, not yet the actual geometric fiber comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechScalars
open IncreasingCechComplex FCurve Chow.AffineBase

universe u
section General
variable {X : Scheme.{u}} {ι : Type u} [LinearOrder ι]
  (M : X.Modules) (U : ι → X.Opens) {R : Type u} [CommRing R]
  (ρ : R →+* Γ(X, ⊤))

/-- Actual bounded Cech cohomology retaining its original base action in the type. -/
def BaseHomology (_ρ : R →+* Γ(X, ⊤)) (n : ℕ) : Type u :=
  (complex U (moduleAbelianSheaf M)).homology n

instance baseHomologyAddCommGroup (n : ℕ) : AddCommGroup (BaseHomology M U ρ n) :=
  inferInstanceAs (AddCommGroup ((complex U (moduleAbelianSheaf M)).homology n))

instance baseHomologyModule (n : ℕ) : Module R (BaseHomology M U ρ n) :=
  Module.compHom ((complex U (moduleAbelianSheaf M)).homology n) ρ

/-- The bounded complex has zero cohomology at and beyond the cardinal bound. -/
theorem baseHomology_subsingleton [Fintype ι] (n : ℕ) (hn : Fintype.card ι ≤ n) :
    Subsingleton (BaseHomology M U ρ n) :=
  AddCommGrpCat.subsingleton_of_isZero
    (((complex U (moduleAbelianSheaf M)).sc n).isZero_homology_of_isZero_X₂
      (complex_isZero U (moduleAbelianSheaf M) n hn))

end General

open IncreasingCechComplex FCurve Chow.AffineBase
variable {R : CommRingCat.{0}} [IsNoetherianRing R] {X : Scheme.{0}}
  (f : X ⟶ Spec R) [IsProper f] [X.IsSeparated]
  (M : X.Modules) [M.IsFinitePresentation] [M.IsQuasicoherent]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

include hU hCover

omit [Finite ι] in
/-- Properness makes the original base-valued bounded cohomology finite. -/
theorem baseHomology_finite (n : ℕ) :
    Module.Finite R (BaseHomology M U (baseCohomologyScalars f) n) :=
  proper_cohomology_finite f M U hU hCover n

/-- One nonzero scalar makes every actual bounded cohomology module projective. -/
theorem exists_generic_projective_cohomology [IsDomain R] :
    ∃ r : R, r ≠ 0 ∧ ∀ n : ℕ,
      Module.Projective (Localization.Away r)
        (LocalizedModule.Away r (BaseHomology M U (baseCohomologyScalars f) n)) := by
  let _ := Fintype.ofFinite ι
  let H := fun n ↦ BaseHomology M U (baseCohomologyScalars f) n
  let _ (n : ℕ) : Module.Finite R (H n) := baseHomology_finite f M U hU hCover n
  let _ (n : ℕ) : Module.FinitePresentation R (H n) :=
    Module.finitePresentation_of_finite R (H n)
  obtain ⟨r, hr, hproj⟩ := Approximation.exists_simultaneous_generic_projective
    (R := R) (fun n : Fin (Fintype.card ι) ↦ H n.val)
  refine ⟨r, hr, fun n ↦ ?_⟩
  by_cases hn : n < Fintype.card ι
  · exact hproj ⟨n, hn⟩
  · let _ : Subsingleton (H n) := baseHomology_subsingleton M U _ n (by omega)
    infer_instance

end FLT.Mazur.IncreasingCechScalars
