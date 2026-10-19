/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeMinimalPrimeFiniteTargetOpen

/-!
# Dense finite target loci over unreduced Noetherian affine bases

The constructed finite locus contains every original minimal prime, so it is
dense on every original component. Its whole scheme restriction is finite.
Density does not assert that an arbitrary prescribed prime lies in this open.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]
  (f : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation f]
  [LocallyQuasiFinite f] [IsSeparated f] [QuasiCompact f]

/-- Every original component meets the actual whole-source finite target locus densely. -/
theorem finiteTargetOpen_dense_of_noetherian_spec :
    Dense (finiteTargetOpen f : Set (Spec (.of R))) := by
  intro P
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (J := P.asIdeal) bot_le
  have hs := (PrimeSpectrum.le_iff_specializes ⟨Q, hQ.1.1⟩ P).mp hQP
  exact hs.mem_closed isClosed_closure
    (subset_closure (minimalPrime_mem_finiteTarget f ⟨Q, hQ.1.1⟩ hQ))

variable {Y : Scheme.{0}} [IsAffine Y] [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [LocallyOfFinitePresentation g] [LocallyQuasiFinite g]
  [IsSeparated g] [QuasiCompact g]

/-- Reducible and nonreduced affine Noetherian targets have dense actual finite loci. -/
theorem finiteTargetOpen_dense_of_noetherian_affine : Dense (finiteTargetOpen g : Set Y) := by
  intro y
  let P := Y.isoSpec.hom y
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (J := P.asIdeal) bot_le
  let z : Spec Γ(Y, ⊤) := ⟨Q, hQ.1.1⟩
  have hz : Y.isoSpec.inv z ∈ finiteTargetOpen g := by
    apply affine_minimalPrime_mem_finiteTarget
    have he : Y.isoSpec.hom (Y.isoSpec.inv z) = z := by
      change (Y.isoSpec.inv ≫ Y.isoSpec.hom) z = z
      simp
    simpa only [he] using hQ
  have hs := ((PrimeSpectrum.le_iff_specializes z P).mp hQP).map Y.isoSpec.inv.continuous
  have he : Y.isoSpec.inv P = y := by
    change (Y.isoSpec.hom ≫ Y.isoSpec.inv) y = y
    simp
  rw [he] at hs
  exact hs.mem_closed isClosed_closure (subset_closure hz)

/-- The dense open is an actual finite restriction, retaining all original preimages. -/
theorem exists_dense_finite_open_of_noetherian_affine :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (g ∣_ U) :=
  ⟨finiteTargetOpen g, finiteTargetOpen_dense_of_noetherian_affine g,
    finite_restrict_finiteTarget g⟩

end FLT.Mazur.SchemeOpenEnvelope
