/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.QuasiCompactMinimalPrimeFiniteOpen
public import FLT.Mazur.SchemeGenericFiniteTargetOpen

/-!
# Original minimal endpoints belong to the actual finite target locus

A separated quasi-finite morphism of finite presentation over a Noetherian
original affine base has a finite whole-source neighborhood at each minimal
prime of that base. Reducibility and nilpotents are retained.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]
  (f : X ⟶ Spec (.of R)) [LocallyOfFinitePresentation f]
  [LocallyQuasiFinite f] [IsSeparated f] [QuasiCompact f]

/-- Every original minimal coefficient prime has a finite restriction of the entire source. -/
theorem minimalPrime_mem_finiteTarget (P : PrimeSpectrum R)
    (hP : P.asIdeal ∈ minimalPrimes R) : P ∈ finiteTargetOpen f := by
  let _ := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨r, hr, hf⟩ := QuasiCompactMinimalPrimeFiniteOpen.exists_finite_principal f P hP
  let j := SpecMinimalPrimeFiniteOpen.targetMap r
  let _ : IsFinite (pullback.snd f j) := hf
  have hl := opensRange_le_finiteTarget_of_isPullback f j _ _
    (IsPullback.of_hasPullback f j)
  apply hl
  exact (SpecMinimalPrimeFiniteOpen.mem_targetMap_range r P).mpr hr

variable {Y : Scheme.{0}} [IsAffine Y] [IsLocallyNoetherian Y]
  (g : X ⟶ Y) [LocallyOfFinitePresentation g] [LocallyQuasiFinite g]
  [IsSeparated g] [QuasiCompact g]

/-- Minimal primes of the original affine section ring retain their actual finite neighborhoods. -/
theorem affine_minimalPrime_mem_finiteTarget (y : Y)
    (hy : (Y.isoSpec.hom y).asIdeal ∈ minimalPrimes Γ(Y, ⊤)) :
    y ∈ finiteTargetOpen g := by
  let _ : IsNoetherianRing Γ(Y, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top Y⟩
  let f := g ≫ Y.isoSpec.hom
  have hp := minimalPrime_mem_finiteTarget f (Y.isoSpec.hom y) hy
  obtain ⟨U, hU, hyU⟩ := (mem_finiteTargetOpen f _).mp hp
  let _ := hU
  have H := (isPullback_morphismRestrict f U).flip.paste_horiz
    (IsPullback.of_horiz_isIso
      (show CommSq (𝟙 X) f g Y.isoSpec.inv from ⟨by simp [f]⟩))
  simp only [Category.comp_id] at H
  have hl := opensRange_le_finiteTarget_of_isPullback g (U.ι ≫ Y.isoSpec.inv) _ _ H
  apply hl
  refine ⟨⟨Y.isoSpec.hom y, hyU⟩, ?_⟩
  change (Y.isoSpec.hom ≫ Y.isoSpec.inv) y = y
  simp

end FLT.Mazur.SchemeOpenEnvelope
