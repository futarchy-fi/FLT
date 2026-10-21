/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryResidualIdeal

/-!
# Simultaneous original residual powers for finite boundary families

Finitely many full original boundary invariants have one original ideal
power. That power lifts every scalar combination of the family, with the
literal full boundary value. Only a finite maximum of exponents is taken;
no infinite family or intersection of radicals is interchanged.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeOpenEnvelope SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] (e : CategoryTheory.EquivalenceRelation p q)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  [IsAffine S] (f : A ⟶ S) (hf : p ≫ f = q ≫ f) [IsSeparated f]
  {ι : Type*} [Fintype ι]
  (t : ι → compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
  (Q : Ideal (compatibleFunctions p q)) (hfg : Q.FG)
variable (hQ :
  closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) '' (J.support : Set A)) ∩
    closure (scalarMorphism (Subring.subtype (compatibleFunctions p q)) ''
      (finiteTargetOpen p : Set A)ᶜ) ⊆
  PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)))

include e hf hfg hQ in
omit [Fintype ι] in
/-- A finite boundary family admits one exponent in the unchanged original scalar ring. -/
theorem exists_pow_le_originalBoundaryLiftIdeals_finite [Finite ι] :
    ∃ N : ℕ, ∀ i, Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J (t i).val := by
  classical
  let _ := Fintype.ofFinite ι
  have H (i : ι) : ∃ N : ℕ,
      Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J (t i).val :=
    exists_pow_le_originalBoundaryLiftIdeal_of_residual (p := p) (q := q)
      J e hJ f hf (t i) Q hfg hQ
  let N : ι → ℕ := fun i ↦ Classical.choose (H i)
  have hN (i : ι) : Q ^ N i ≤ originalBoundaryLiftIdeal (p := p) (q := q) J (t i).val :=
    Classical.choose_spec (H i)
  refine ⟨Finset.univ.sup N, fun i ↦ ?_⟩
  exact (Ideal.pow_le_pow_right (I := Q) (Finset.le_sup (f := N) (Finset.mem_univ i))).trans (hN i)

private theorem lift_finite_combination {R B κ : Type*} [CommRing R] [CommRing B]
    [Fintype κ] (b : R →+* B) (s : R) (t : κ → B)
    (h : ∀ i, ∃ w : R, b w = b s * t i) (a : κ → R) :
    ∃ w : R, b w = b s * ∑ i, b (a i) * t i := by
  classical
  choose w hw using h
  refine ⟨∑ i, a i * w i, ?_⟩
  simp only [map_sum, map_mul, hw, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ mul_left_comm _ _ _)

include e hf hfg hQ in
/-- The same power lifts every original scalar combination of all listed boundary invariants. -/
theorem exists_pow_lifting_originalBoundary_finite_combinations :
    ∃ N : ℕ, ∀ s ∈ Q ^ N, ∀ a : ι → compatibleFunctions p q,
      ∃ w : compatibleFunctions p q, J.subschemeι.appTop w.val =
        J.subschemeι.appTop s.val * ∑ i, J.subschemeι.appTop (a i).val * (t i).val := by
  classical
  obtain ⟨N, hN⟩ := exists_pow_le_originalBoundaryLiftIdeals_finite e J hJ f hf t Q hfg hQ
  refine ⟨N, fun s hs a ↦ ?_⟩
  let b := J.subschemeι.appTop.hom.comp (compatibleFunctions p q).subtype
  exact lift_finite_combination b s (fun i ↦ (t i).val) (fun i ↦ hN i hs) a

end FLT.Mazur.EquivalenceRelationOrderedFrames
