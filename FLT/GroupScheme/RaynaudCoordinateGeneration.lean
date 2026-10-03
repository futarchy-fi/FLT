/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudDigitMonomialGeneration

/-!
# Generation of the actual coordinate algebra

The character projector decomposition generates the augmentation ideal
from the proved character bases. The counit splitting then adds the
constants and proves generation of the whole coordinate algebra.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing CharacterProjector

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x) (e : F →+* ResidueField R)

include h0 hadd in
/-- Every augmentation vector is in the algebra of actual fundamental coordinates. -/
theorem FF.augmentation_mem_fundamental_adjoin (v : X.augmentation) :
    (v : X.CoordinateRing) ∈
      Algebra.adjoin R (Set.range (X.fundamentalCoordinate p lift h1 hmul hdim hlift e)) := by
  classical
  obtain ⟨hr, _, _⟩ := henselian_group_characters (R := R) Fˣ (by
    rw [scalar_units_card_residue (F := F) p]; exact neg_ne_zero.mpr one_ne_zero)
  let : HasEnoughRootsOfUnity R (Monoid.exponent Fˣ) := hr
  let : Fintype (Fˣ →* Rˣ) := Fintype.ofFinite _
  let S := Algebra.adjoin R
    (Set.range (X.fundamentalCoordinate p lift h1 hmul hdim hlift e))
  have hmem (ψ : Fˣ →* Rˣ) :
      ((projector (X.augmentationRepresentation lift h1 hmul) ψ v : X.augmentation) :
        X.CoordinateRing) ∈ S := by
    let w : X.integralCharacter lift h1 hmul ψ :=
      ⟨projector (X.augmentationRepresentation lift h1 hmul) ψ v, projector_mem _ _ _⟩
    let b := X.characterBasis lift h1 hmul p hdim hlift ψ
    have hw : b.repr w () • b () = w := by simpa using b.sum_repr w
    have hg := S.smul_mem
      (X.characterGenerator_mem_adjoin lift h0 h1 hmul hadd p hdim hlift e ψ) (b.repr w ())
    change ((b.repr w () • b ()).val : X.CoordinateRing) ∈ S at hg
    rwa [hw] at hg
  have hsum := S.sum_mem (fun ψ (_ : ψ ∈ Finset.univ) ↦ hmem ψ)
  have heq := congrArg (fun w : X.augmentation ↦ (w : X.CoordinateRing))
    (sum_projector (X.augmentationRepresentation lift h1 hmul) v)
  simp only [Submodule.coe_sum] at heq
  rwa [heq] at hsum

include h0 hadd in
/-- Fundamental coordinates generate the full coordinate algebra, not just its generic fiber. -/
theorem FF.fundamental_adjoin_eq_top :
    Algebra.adjoin R (Set.range (X.fundamentalCoordinate p lift h1 hmul hdim hlift e)) = ⊤ := by
  apply top_unique
  intro x hx
  let v := (X.augmentationSplit x).2
  have hv := X.augmentation_mem_fundamental_adjoin lift h0 h1 hmul hadd p hdim hlift e v
  have hc := (Algebra.adjoin R (Set.range
    (X.fundamentalCoordinate p lift h1 hmul hdim hlift e))).algebraMap_mem
    (Coalgebra.counit x)
  have hs := Subalgebra.add_mem _ hc hv
  simpa [v, FF.augmentationSplit] using hs

end ThreeAdicPlan
