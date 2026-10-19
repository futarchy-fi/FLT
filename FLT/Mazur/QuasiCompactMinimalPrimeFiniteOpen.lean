/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineMinimalPrimeFiniteOpen
public import FLT.Mazur.QuasiCompactGenericFiniteOpen

/-!
# Whole-source finite neighborhoods at original minimal primes

A finite affine cover of the entire source has a finite pullback on one
original principal target open. Surjective descent of universal closedness,
separatedness and quasi-finiteness then make the entire source finite there.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.QuasiCompactMinimalPrimeFiniteOpen
open SpecMinimalPrimeFiniteOpen QuasiCompactGenericFlatOpen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme} [CompactSpace X]
  (g : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation g]
  [LocallyQuasiFinite g] [IsSeparated g]

/-- Every minimal original prime has a finite restriction of the entire separated source. -/
theorem exists_finite_principal (P : PrimeSpectrum R) (hP : P.asIdeal ∈ minimalPrimes R) :
    ∃ r : R, r ∉ P.asIdeal ∧
      IsFinite (pullback.snd g (SpecMinimalPrimeFiniteOpen.targetMap r)) := by
  let p := affineCoverMap X
  obtain ⟨r, hr, hfin⟩ := AffineMinimalPrimeFiniteOpen.exists_finite_principal (p ≫ g) P hP
  refine ⟨r, hr, ?_⟩
  let j := SpecMinimalPrimeFiniteOpen.targetMap r
  let e : pullback (p ≫ g) j ⟶ pullback g j :=
    pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _) (by
      rw [Category.assoc]
      exact pullback.condition)
  have he₁ : e ≫ pullback.snd g j = pullback.snd (p ≫ g) j :=
    pullback.lift_snd _ _ _
  have he₂ : e ≫ pullback.fst g j = pullback.fst (p ≫ g) j ≫ p :=
    pullback.lift_fst _ _ _
  have H : IsPullback e (pullback.fst (p ≫ g) j) (pullback.fst g j) p := by
    apply IsPullback.of_right _ he₂ (IsPullback.of_hasPullback g j).flip
    rw [he₁]
    exact (IsPullback.of_hasPullback (p ≫ g) j).flip
  let _ : Surjective e := MorphismProperty.of_isPullback H.flip inferInstance
  let _ : IsFinite (pullback.snd (p ≫ g) j) := hfin
  let _ : UniversallyClosed (e ≫ pullback.snd g j) := by
    rw [he₁]
    infer_instance
  let _ : UniversallyClosed (pullback.snd g j) :=
    UniversallyClosed.of_comp_surjective e (pullback.snd g j)
  let _ : IsProper (pullback.snd g j) := ⟨⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

end FLT.Mazur.QuasiCompactMinimalPrimeFiniteOpen
