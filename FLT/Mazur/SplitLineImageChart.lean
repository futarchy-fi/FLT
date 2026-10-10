/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitLineCoordinateCover
public import FLT.Mazur.NormalizedSectionLineSheaf

/-!
# Recovering normalized charts of actual split line inclusions

A chosen frame of an arbitrary rank-one source module determines its image
vector. The constructed coordinate chart has exactly the original inclusion's
range, and its line sheaf is isomorphic to the original source sheaf through
an isomorphism that preserves the actual ambient inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SplitLineImageChart
open NormalizedSectionLine
variable {R : Type u} [CommRing R] {ι P : Type u} [AddCommGroup P] [Module R P]
variable (s : P →ₗ[R] (ι → R)) (r : (ι → R) →ₗ[R] P)
variable (hs : r.comp s = LinearMap.id) (e : P ≃ₗ[R] R)

include hs in
/-- The retraction proves injectivity of the original inclusion. -/
lemma injective : Function.Injective s := by
  intro x y h
  have he := congrArg r h
  change (r.comp s) x = (r.comp s) y at he
  simpa only [hs, LinearMap.id_apply] using he

/-- The image vector from a frame generates exactly the original inclusion's range. -/
lemma range_eq_generator : LinearMap.range s =
    LinearMap.range (LinearMap.toSpanSingleton R (ι → R) (s (e.symm 1))) := by
  apply le_antisymm
  · rintro v ⟨x, rfl⟩
    refine ⟨e x, ?_⟩
    change e x • s (e.symm 1) = s x
    rw [← s.map_smul]
    congr 1
    apply e.injective
    simp only [e.map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  · rintro v ⟨a, rfl⟩
    exact ⟨a • e.symm 1, s.map_smul a _⟩

include hs in
/-- The coordinate principal opens of an actual split line cover its affine base. -/
lemma principal_cover [Finite ι] :
    (⨆ i, PrimeSpectrum.basicOpen (s (e.symm 1) i)) = ⊤ := by
  apply generator_basicOpen_cover _ (e.toLinearMap.comp r)
  change e ((r.comp s) (e.symm 1)) = 1
  rw [hs, LinearMap.id_apply, e.apply_symm_apply]

variable (i : ι) (a : Rˣ) (hi : s (e.symm 1) i = a)

/-- The normalized image chart is constructed from the original inclusion and its frame. -/
abbrev chart : Chart R ι i := unitCoordinateLine (s (e.symm 1)) i a hi

/-- The chart retains the actual image of the original inclusion. -/
lemma chart_val : (chart s e i a hi).val = LinearMap.range s :=
  (range_eq_generator s e).symm

/-- The actual source line identifies with the constructed image chart. -/
def sourceIso : P ≃ₗ[R] (chart s e i a hi).val :=
  (LinearEquiv.ofInjective s (injective s r hs)).trans
    (LinearEquiv.ofEq _ _ (chart_val s e i a hi).symm)

/-- The source comparison preserves the original linear inclusion. -/
lemma sourceIso_subtype :
    (chart s e i a hi).val.subtype.comp (sourceIso s r hs e i a hi).toLinearMap = s := by
  ext x j
  rfl

/-- The original affine source sheaf is the constructed normalized line sheaf. -/
def sheafSourceIso : tilde (ModuleCat.of R P) ≅ sheaf i (chart s e i a hi) :=
  (tilde.functor (.of R)).mapIso (sourceIso s r hs e i a hi).toModuleIso

/-- The sheaf comparison retains the actual original ambient inclusion. -/
lemma sheafSourceIso_inclusion :
    (sheafSourceIso s r hs e i a hi).hom ≫ sheafInclusion i (chart s e i a hi) =
      (tilde.functor (.of R)).map (ModuleCat.ofHom s) := by
  change (tilde.functor (.of R)).map _ ≫ (tilde.functor (.of R)).map _ = _
  rw [← Functor.map_comp]
  congr 1

end FLT.Mazur.SplitLineImageChart
