/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Equations of a principal open are exactly parameter-power torsion

The full section kernel on each affine patch is computed without reducing
the ambient ring. In particular, nilpotents and embedded components remain.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffinePrincipalKernel
variable {X : Scheme} (t : Γ(X, ⊤)) (U : X.affineOpens)

/-- Restriction from global functions to the actual affine patch. -/
abbrev restriction : Γ(X, ⊤) ⟶ Γ(X, U) :=
  X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op
local notation "ρ" => restriction U

/-- The exact section kernel of the principal-open inclusion on an arbitrary affine patch. -/
theorem equation_iff (z : Γ(X, U)) :
    (X.basicOpen t).ι.app U z = 0 ↔ ∃ n : ℕ, (ρ) t ^ n * z = 0 := by
  let u := (ρ) t
  have he : (X.basicOpen t).ι ''ᵁ ((X.basicOpen t).ι ⁻¹ᵁ U.1) = X.basicOpen u := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact (inf_comm _ _).trans
      (X.basicOpen_res t (homOfLE (show U.1 ≤ ⊤ from le_top)).op).symm
  change X.presheaf.map (homOfLE (x := (X.basicOpen t).ι ''ᵁ
    ((X.basicOpen t).ι ⁻¹ᵁ U.1)) (y := U.1) (Set.image_preimage_subset _ _)).op z = 0 ↔ _
  rw! [he]
  let _ := U.2.isLocalization_basicOpen u
  change algebraMap Γ(X, U) Γ(X, X.basicOpen u) z = 0 ↔ ∃ n : ℕ, u ^ n * z = 0
  rw [IsLocalization.map_eq_zero_iff (.powers u)]
  constructor
  · rintro ⟨⟨a, ⟨n, rfl⟩⟩, hz⟩
    exact ⟨n, hz⟩
  · rintro ⟨n, hz⟩
    exact ⟨⟨u ^ n, ⟨n, rfl⟩⟩, hz⟩

end FLT.Mazur.AffinePrincipalKernel
