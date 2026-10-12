/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientSheaf

/-!
# Fixed-rank principal bases for the original Grassmannian quotient

The original quotient rank gives actual principal-local bases indexed by `Fin d`,
not merely an unspecified finite set. These supply fixed-rank affine data for
subsequent sheaf descent.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A M : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] {d : ℕ}
variable (N : Module.Grassmannian A (A ⊗[R] M) d)

/-- Each prime has a principal neighborhood with a basis of the prescribed quotient rank. -/
theorem grassmannianQuotient_localBasis (p : PrimeSpectrum A) :
    ∃ r ∉ p.asIdeal, Nonempty (Module.Basis (Fin d) (Localization.Away r)
      (LocalizedModule.Away r ((A ⊗[R] M) ⧸ N.toSubmodule))) := by
  let Q := (A ⊗[R] M) ⧸ N.toSubmodule
  let _ := Module.finitePresentation_of_projective A Q
  let _ : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal Q) := Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hf, hd⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl Q)
    (Localization.AtPrime p.asIdeal)
  let _ := hf
  let j : Localization.Away r →+* Localization.AtPrime p.asIdeal :=
    IsLocalization.map (M := .powers r) (T := p.asIdeal.primeCompl) _
      (RingHom.id _) (Submonoid.powers_le.mpr hr)
  let _ := j.domain_nontrivial
  have hd' : Module.finrank (Localization.Away r) (LocalizedModule.Away r Q) = d :=
    hd.trans (N.rankAtStalk_eq p)
  exact ⟨r, hr, ⟨(Module.finBasis (Localization.Away r)
    (LocalizedModule.Away r Q)).reindex (finCongr hd')⟩⟩

end FLT.Mazur.GrassmannianChart
