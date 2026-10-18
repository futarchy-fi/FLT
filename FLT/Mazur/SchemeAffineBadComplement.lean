/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarIntegralBadCover

/-!
# Constructing the affine bad complement

For every open of an independently fixed affine target, the quotient by its
complement's vanishing ideal gives an actual affine bad cover. More generally,
any ideal with the same zero locus gives a possibly nonreduced bad cover.
The ambient target and original scalar ring are unchanged.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} [IsAffine X]

/-- The ideal defining the reduced bad complement of an affine target open. -/
def affineBadIdeal (O : X.Opens) : Ideal Γ(X, ⊤) :=
  PrimeSpectrum.vanishingIdeal (X.toSpecΓ '' (O : Set X)ᶜ)

/-- The bad complement's defining ideal has exactly the required zero locus. -/
theorem zeroLocus_affineBadIdeal (O : X.Opens) :
    PrimeSpectrum.zeroLocus (affineBadIdeal O : Set Γ(X, ⊤)) =
      X.toSpecΓ '' (O : Set X)ᶜ := by
  rw [affineBadIdeal, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  exact (X.toSpecΓ.homeomorph.isClosedMap _ O.isOpen.isClosed_compl).closure_eq

/-- Quotient coordinates construct an affine scheme without reducing the given ideal. -/
def affineClosedComplement (J : Ideal Γ(X, ⊤)) : Scheme :=
  Spec (.of (Γ(X, ⊤) ⧸ J))

instance (J : Ideal Γ(X, ⊤)) : IsAffine (affineClosedComplement J) :=
  inferInstanceAs (IsAffine (Spec (.of (Γ(X, ⊤) ⧸ J))))

/-- The actual quotient morphism into the independently fixed affine target. -/
def affineClosedComplementMap (J : Ideal Γ(X, ⊤)) : affineClosedComplement J ⟶ X :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ X.isoSpec.inv

/-- Taking target coordinates recovers the quotient's spectrum map. -/
theorem affineClosedComplementMap_toSpecΓ (J : Ideal Γ(X, ⊤)) :
    affineClosedComplementMap J ≫ X.toSpecΓ =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
  rw [affineClosedComplementMap, Category.assoc, Scheme.isoSpec_inv_toSpecΓ]
  exact Category.comp_id _

/-- The quotient morphism covers precisely the prescribed closed subset. -/
theorem range_affineClosedComplementMap (J : Ideal Γ(X, ⊤)) :
    Set.range (affineClosedComplementMap J) =
      X.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus (J : Set Γ(X, ⊤)) := by
  have hr : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) =
      PrimeSpectrum.zeroLocus (J : Set Γ(X, ⊤)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  ext x
  rw [Set.mem_preimage, ← hr]
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, congrArg (fun g : affineClosedComplement J ⟶ Spec Γ(X, ⊤) ↦ g b)
      (affineClosedComplementMap_toSpecΓ J).symm⟩
  · rintro ⟨b, hb⟩
    refine ⟨b, X.toSpecΓ.homeomorph.injective ?_⟩
    exact (congrArg (fun g : affineClosedComplement J ⟶ Spec Γ(X, ⊤) ↦ g b)
      (affineClosedComplementMap_toSpecΓ J)).trans hb

/-- An ideal with the required zero locus supplies the bad cover, including thickenings. -/
theorem affineClosedComplementMap_covers (O : X.Opens) (J : Ideal Γ(X, ⊤))
    (hJ : PrimeSpectrum.zeroLocus (J : Set Γ(X, ⊤)) = X.toSpecΓ '' (O : Set X)ᶜ) :
    Set.range (affineClosedComplementMap J) = (O : Set X)ᶜ := by
  rw [range_affineClosedComplementMap, hJ]
  exact Set.preimage_image_eq _ X.toSpecΓ.homeomorph.injective

/-- Every independently fixed affine target has an explicit affine bad-complement cover. -/
theorem affineBadComplement_covers (O : X.Opens) :
    Set.range (affineClosedComplementMap (affineBadIdeal O)) = (O : Set X)ᶜ :=
  affineClosedComplementMap_covers O (affineBadIdeal O) (zeroLocus_affineBadIdeal O)

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
