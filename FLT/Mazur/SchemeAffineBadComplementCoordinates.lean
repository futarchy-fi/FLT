/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineBadComplement

/-!
# Exact coordinates of the constructed bad complement

Pullback to the quotient complement has kernel exactly the chosen ideal,
including its nilpotent thickening. The original scalar kernel is its
contraction. Thus safe-prime tests can be made in the actual target ring.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [IsAffine X]
  (s : R →+* Γ(X, ⊤)) (J : Ideal Γ(X, ⊤))

/-- Pullback into quotient coordinates is the original quotient homomorphism. -/
theorem affineClosedComplementMap_coordinates :
    (affineClosedComplementMap J).appTop ≫
      (Scheme.ΓSpecIso (.of (Γ(X, ⊤) ⧸ J))).hom =
      CommRingCat.ofHom (Ideal.Quotient.mk J) := by
  apply (cancel_epi (Scheme.ΓSpecIso Γ(X, ⊤)).hom).mp
  rw [← Category.assoc, ← Scheme.toSpecΓ_appTop,
    ← Scheme.Hom.comp_appTop, affineClosedComplementMap_toSpecΓ,
    Scheme.ΓSpecIso_naturality, Scheme.toSpecΓ_appTop]
  rfl

/-- Vanishing on the actual bad scheme is membership in its exact defining ideal. -/
theorem affineClosedComplementMap_apply_eq_zero_iff (x : Γ(X, ⊤)) :
    (affineClosedComplementMap J).appTop x = 0 ↔ x ∈ J := by
  let e := (Scheme.ΓSpecIso (.of (Γ(X, ⊤) ⧸ J))).commRingCatIsoToRingEquiv
  have he : e ((affineClosedComplementMap J).appTop x) = Ideal.Quotient.mk J x :=
    congrArg (fun f : Γ(X, ⊤) ⟶ CommRingCat.of (Γ(X, ⊤) ⧸ J) ↦ f x)
      (affineClosedComplementMap_coordinates J)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hx
    exact he.symm.trans (hx ▸ e.map_zero)
  · intro hx
    apply e.injective
    exact he.trans (hx.trans e.map_zero.symm)

/-- The original scalar kernel is computed without discarding nilpotents. -/
theorem affineClosedComplementMap_scalar_kernel :
    RingHom.ker ((affineClosedComplementMap J).appTop.hom.comp s) = Ideal.comap s J := by
  ext r
  exact affineClosedComplementMap_apply_eq_zero_iff J (s r)

/-- For any defining ideal of the bad complement, avoidance is its radical contraction. -/
theorem scalarAvoidanceIdeal_eq_affineBad_comap (O : X.Opens)
    (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(X, ⊤)) = X.toSpecΓ '' (O : Set X)ᶜ) :
    scalarAvoidanceIdeal s O = (Ideal.comap s J).radical := by
  rw [scalarAvoidanceIdeal_eq_badCover_ker_radical s O (affineClosedComplementMap J)
    (affineClosedComplementMap_covers O J hJ), affineClosedComplementMap_scalar_kernel]

/-- An original safe prime gives an exact annihilator on any chosen bad thickening. -/
theorem exists_scalar_mem_affineBad (O : X.Opens)
    (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(X, ⊤)) = X.toSpecΓ '' (O : Set X)ᶜ)
    (P : PrimeSpectrum R) (hP : P ∈ scalarNeighborhoodLocus s O) :
    ∃ r : R, r ∉ P.asIdeal ∧ s r ∈ J ∧ X.basicOpen (s r) ≤ O := by
  obtain ⟨r, hr, hz, hO⟩ := exists_scalar_killing_badCover s O (affineClosedComplementMap J)
    (affineClosedComplementMap_covers O J hJ) P hP
  exact ⟨r, hr, (affineClosedComplementMap_apply_eq_zero_iff J (s r)).mp hz, hO⟩

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
