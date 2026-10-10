/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatCoefficientAllCohomology
public import FLT.Mazur.SpectrumFieldCohomologyCoordinates

/-!
# Field base change preserves actual cohomology dimensions

For a cartesian square over field spectra, every actual quasi-coherent
cohomology group keeps its dimension over the original field coordinates.
No finite-dimensionality hypothesis or choice of a basis is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules hiding map_smul
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.IncreasingCechCoefficients
open FCurve SpectrumFieldCohomologyCoordinates
variable {k K : Type} [Field k] [Field K]
  {P X : Scheme.{0}} [X.IsSeparated]
  {p : P ⟶ X} {q : P ⟶ Spec (CommRingCat.of K)}
  {f : X ⟶ Spec (CommRingCat.of k)}
  {g : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)}
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

include h hU hCover

/-- Actual cohomology dimensions are invariant under an arbitrary extension of base fields. -/
theorem field_cohomology_finrank (n : ℕ) :
    Module.finrank K (ModuleScalarH q ((pullback p).obj M) n) =
      Module.finrank k (ModuleScalarH f M n) := by
  let _ := globalSectionsField k
  let _ := globalSectionsField K
  let _ := g.appTop.hom.toAlgebra
  let _ : Module.Free Γ(Spec (CommRingCat.of k), ⊤)
      Γ(Spec (CommRingCat.of K), ⊤) := Module.Free.of_divisionRing _ _
  have hg : g.appTop.hom.Flat := Module.Flat.of_free
  rw [← cohomology_finrank q, ← cohomology_finrank f]
  exact (flatCohomologyEquiv h M U hU hCover hg n).finrank_eq.symm.trans
    (Module.finrank_baseChange (R := Γ(Spec (CommRingCat.of K), ⊤))
      (S := Γ(Spec (CommRingCat.of k), ⊤)) (M' := ModuleRingH f.appTop.hom M n))

end FLT.Mazur.IncreasingCechCoefficients
