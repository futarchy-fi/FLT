/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryScalarNilpotence

/-!
# The full boundary product over an original scalar local scheme

Base change to the stalk at an original scalar prime retains precisely all
product points whose scalar centers generize that prime. This construction
keeps the entire local coefficient scheme, including its nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (P : PrimeSpectrum T)
set_option quotPrecheck false
local notation "S" => Spec (.of T)
local notation "π" => boundaryScalarProjection s κ
local notation "ι" => (S).fromSpecStalk P

/-- The unchanged full boundary product after localization at the original scalar center. -/
def boundaryScalarLocalProduct : Scheme := pullback π ι

/-- The projection back to the full original coefficient scheme. -/
def boundaryScalarLocalMap : boundaryScalarLocalProduct s κ P ⟶ boundaryProduct s κ :=
  pullback.fst _ _

instance boundaryScalarLocalProduct_affine : IsAffine (boundaryScalarLocalProduct s κ P) := by
  unfold boundaryScalarLocalProduct
  infer_instance

/-- Exactly the product points with generizing scalar centers survive full scalar localization. -/
theorem boundaryScalarLocalMap_range :
    Set.range (boundaryScalarLocalMap s κ P) =
      {z : boundaryProduct s κ | (π z).asIdeal ≤ P.asIdeal} := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    apply (PrimeSpectrum.le_iff_specializes _ _).mpr
    have hx : π (boundaryScalarLocalMap s κ P x) ∈ Set.range ι := by
      refine ⟨pullback.snd π ι x, ?_⟩
      exact (congrArg (fun f ↦ f x) (pullback.condition (f := π) (g := ι))).symm
    rwa [Scheme.range_fromSpecStalk] at hx
  · intro hz
    have hr : π z ∈ Set.range ι := by
      rw [Scheme.range_fromSpecStalk]
      exact (PrimeSpectrum.le_iff_specializes _ _).mp hz
    obtain ⟨y, hy⟩ := hr
    obtain ⟨x, hx, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := π) (g := ι) z y hy.symm
    exact ⟨x, hx⟩

/-- Every original product component with a relevant scalar center has an actual local lift. -/
theorem boundaryScalarLocalMap_component_lift
    (Q : minimalPrimes Γ(boundaryProduct s κ, ⊤))
    (hQ : (π (boundaryComponentPoint s κ Q)).asIdeal ≤ P.asIdeal) :
    ∃ x : boundaryScalarLocalProduct s κ P,
      boundaryScalarLocalMap s κ P x = boundaryComponentPoint s κ Q := by
  apply Set.mem_range.mp
  rw [boundaryScalarLocalMap_range]
  exact hQ

end FLT.Mazur.AffineScalarBoundaryNilpotence
