/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOriginalScalarOpenCorrections

/-!
# One original denominator for independent target corrections

Finitely many independent stable image domains can require different
original scalars and powers. Their product constructs one scalar outside the
same original prime and exact boundary-zero corrections on all fixed targets.
The full finite families of relation errors are multiplied by that same scalar.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteGroupQuotient
open FiniteGroupRestriction SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {ι : Type} [Finite ι]
  {G : ι → Type} [∀ a, Group (G a)] [∀ a, Finite (G a)]
  {X Y : ι → Scheme} [∀ a, IsAffine (X a)] [∀ a, IsAffine (Y a)]
  (ρ : ∀ a, G a →* Aut (X a)) (σ : ∀ a, R →+* invariantCoordinates (ρ a))
  (O : ∀ a, (X a).Opens) (hO : ∀ a g, (ρ a g).hom ⁻¹ᵁ O a = O a)
  (i : ∀ a, Y a ⟶ X a) {J : ι → Type} [∀ a, Finite (J a)]
  {Z : ∀ a, J a → Scheme} [∀ a b, IsAffine (Z a b)]
  (F H : ∀ a b, Z a b ⟶ X a)
  (hσ : ∀ a b r, (F a b).appTop (σ a r).val = (H a b).appTop (σ a r).val)
  (FO HO : ∀ a b, Z a b ⟶ (O a).toScheme)
  (hF : ∀ a b, FO a b ≫ (O a).ι = F a b)
  (hH : ∀ a b, HO a b ≫ (O a).ι = H a b)

include hσ hF hH in
/-- Geometric image-domain lifts give simultaneous corrections with one original denominator. -/
theorem originalScalar_open_relation_correction_family (P : PrimeSpectrum R)
    (hP : ∀ a, P ∈ scalarNeighborhoodLocus (invariantScalarCoordinates (ρ a) (σ a)) (O a))
    (v : ∀ a, invariantCoordinates (restrictedAction (ρ a) (O a) (hO a)))
    (u : ∀ a, invariantCoordinates (ρ a))
    (hb : ∀ a, ((i a) ∣_ O a).appTop (v a).val =
      ((i a) ⁻¹ᵁ O a).ι.appTop ((i a).appTop (u a).val))
    (he : ∀ a b, (FO a b).appTop (v a).val = (HO a b).appTop (v a).val) :
    ∃ r : R, r ∉ P.asIdeal ∧ ∃ w : ∀ a, invariantCoordinates (ρ a),
      (∀ a, (i a).appTop (w a).val = 0) ∧ ∀ a b,
        (F a b).appTop (w a).val - (H a b).appTop (w a).val =
          (F a b).appTop (σ a r).val *
            ((F a b).appTop (u a).val - (H a b).appTop (u a).val) := by
  classical
  let _ := Fintype.ofFinite ι
  have h (a : ι) := originalScalar_open_relation_correction
    (ρ a) (σ a) (O a) (hO a) (i a) (F a) (H a) (hσ a)
    (FO a) (HO a) (hF a) (hH a) P (hP a) (v a) (u a) (hb a) (he a)
  choose r hr w hw hd using h
  let s := ∏ a, r a
  let c (a : ι) := ∏ b ∈ Finset.univ.erase a, r b
  have hc (a : ι) : c a * r a = s :=
    Finset.prod_erase_mul Finset.univ r (Finset.mem_univ a)
  have hs : s ∈ P.asIdeal.primeCompl :=
    P.asIdeal.primeCompl.prod_mem (fun a _ ↦ hr a)
  refine ⟨s, hs, fun a ↦ σ a (c a) * w a, ?_, ?_⟩
  · intro a
    change (i a).appTop ((σ a (c a)).val * (w a).val) = 0
    rw [map_mul, hw a, mul_zero]
  · intro a b
    change (F a b).appTop ((σ a (c a)).val * (w a).val) -
      (H a b).appTop ((σ a (c a)).val * (w a).val) = _
    rw [map_mul, map_mul, ← hσ a b, ← mul_sub, hd a b, ← mul_assoc]
    have hcoeff : (F a b).appTop (σ a (c a)).val *
        (F a b).appTop (σ a (r a)).val = (F a b).appTop (σ a s).val := by
      rw [← map_mul, ← Subring.coe_mul, ← map_mul, hc a]
    rw [hcoeff]

end FLT.Mazur.SchemeFiniteGroupQuotient
