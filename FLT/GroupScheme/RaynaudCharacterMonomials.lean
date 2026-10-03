/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudPairedCharacterBases

/-!
# Integral coefficients of mixed character monomials

Nonempty products lie in the augmentation eigenspace for the product
character. Its derived basis gives an integral coefficient on both models.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open CharacterProjector IsLocalRing

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K] [Field F]
  (X : FF R K) (lift : F → ModelHom X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))

/-- A nonempty product of integral character vectors has the product character. -/
def FF.integralCharacterProd (cs : List (Fˣ →* Rˣ)) (hne : cs ≠ [])
    (v : ∀ χ, X.integralCharacter lift h1 hmul χ) :
    X.integralCharacter lift h1 hmul cs.prod :=
  ⟨⟨(cs.map (fun χ ↦ ((v χ).val : X.CoordinateRing))).prod, by
    obtain ⟨χ, cs, rfl⟩ := List.exists_cons_of_ne_nil hne
    change (Bialgebra.counitAlgHom R X.CoordinateRing) _ = 0
    simp only [List.map_cons, List.prod_cons, map_mul]
    change Coalgebra.counit ((v χ).val : X.CoordinateRing) * _ = 0
    rw [(v χ).val.property, zero_mul]⟩, by
    apply (mem_eigenspace_iff _ _ _).mpr
    intro u
    apply Subtype.ext
    change lift u (cs.map (fun χ ↦ ((v χ).val : X.CoordinateRing))).prod =
      (cs.prod u : R) • (cs.map (fun χ ↦ ((v χ).val : X.CoordinateRing))).prod
    clear hne
    induction cs with
    | nil => simp
    | cons χ cs ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, MonoidHom.mul_apply, Units.val_mul]
      rw [X.integralCharacter_scalar lift h1 hmul χ (v χ) u, ih, smul_mul_smul_comm]⟩

variable [IsDomain R] [IsPrincipalIdealRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)] [CharZero K] [IsFractionRing R K]
  [Finite F] [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)] [Module F X.Points]
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x)

omit [Fintype Fˣ] [Invertible (Fintype.card Fˣ : R)] in
/-- Every nonempty original character monomial has a derived integral coefficient. -/
theorem FF.character_monomial_relation (cs : List (Fˣ →* Rˣ)) (hne : cs ≠ []) :
    ∃ a : R, (cs.map (X.characterGenerator lift h1 hmul p hdim hlift)).prod =
      a • X.characterGenerator lift h1 hmul p hdim hlift cs.prod := by
  let b := X.characterBasis lift h1 hmul p hdim hlift cs.prod
  let v := X.integralCharacterProd lift h1 hmul cs hne
    (fun χ ↦ X.characterBasis lift h1 hmul p hdim hlift χ ())
  refine ⟨b.repr v (), ?_⟩
  have h : b.repr v () • b () = v := by simpa using b.sum_repr v
  exact (congrArg (fun z : X.integralCharacter lift h1 hmul cs.prod ↦
    (z.val : X.CoordinateRing)) h).symm

/-- The paired dual monomial also has a derived integral coefficient. -/
theorem FF.dual_character_monomial_relation (cs : List (Fˣ →* Rˣ)) (hne : cs ≠ []) :
    ∃ b : R, (cs.map (X.dualCharacterGenerator lift h1 hmul p hdim hlift)).prod =
      b • X.dualCharacterGenerator lift h1 hmul p hdim hlift cs.prod := by
  let b := X.dualCharacterBasis lift h1 hmul p hdim hlift cs.prod
  let v := X.cartierDual.integralCharacterProd (fun u ↦ (lift u).cartierDual)
    (X.dualScalar_one lift h1) (X.dualScalar_mul lift hmul) cs hne
    (fun χ ↦ X.dualCharacterBasis lift h1 hmul p hdim hlift χ ())
  refine ⟨b.repr v (), ?_⟩
  have h : b.repr v () • b () = v := by simpa using b.sum_repr v
  exact (congrArg (fun z : eigenspace (X.dualAugmentationRepresentation lift h1 hmul) cs.prod ↦
    (z.val : X.cartierDual.CoordinateRing)) h).symm

end ThreeAdicPlan
