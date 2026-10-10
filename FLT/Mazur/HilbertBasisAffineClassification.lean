/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBasisAffineFactorization
public import FLT.Mazur.HilbertBasisSchemeBaseChange
public import FLT.Mazur.HilbertBasisSchemeGlobal

/-!
# The classifying parameter on every affine test

Composing an affine factorization with the glued chart morphism gives exactly
the spectrum of the ideal-classifying parameter of the extended quotient.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable (S : Type u) [CommRing S] [Algebra R S] (J : Ideal (MvPolynomial I S))
variable [Module.FinitePresentation S (MvPolynomial I S ⧸ J)]
variable [Module.Flat S (MvPolynomial I S ⧸ J)]
variable (T : Type u) [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Every affine test of the intrinsic locus recovers the actual ideal-classifying parameter. -/
theorem intrinsicChartMorphism_affineTest
    (h : ∃ b : Module.Basis (Fin d) T
      (MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T))),
      ∀ i, polynomialBasisTuple R I d w T
        (J.map (MvPolynomial.map (algebraMap S T))) i = b i)
    (f : Spec (.of T) ⟶ polynomialBasisScheme R I d w S J)
    (hf : f ≫ Scheme.Opens.ι (X := Spec (.of S)) (polynomialBasisOpen R I d w S J) =
      Spec.map (CommRingCat.ofHom (algebraMap S T))) :
    f ≫ intrinsicChartMorphism R I d w S J =
      Spec.map (CommRingCat.ofHom (idealClassifyingMap R I d w T
        ⟨J.map (MvPolynomial.map (algebraMap S T)), h⟩).toRingHom) := by
  let _ := polynomialQuotient_finitePresentation_baseChange I S J T
  let K : PrescribedBasisIdeals R I d w T := ⟨J.map (MvPolynomial.map (algebraMap S T)), h⟩
  let i := Scheme.Opens.ι (X := Spec (.of T)) (polynomialBasisOpen R I d w T K.val)
  have ht : polynomialBasisOpen R I d w T K.val = ⊤ := by
    apply (intrinsicBasisOpen_eq_top_iff (R := T) _).mpr
    obtain ⟨b, hb⟩ := h
    exact ⟨b, fun j ↦ (hb j).symm⟩
  have hr : Set.range (𝟙 (Spec (.of T))) ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]
    intro p _
    change p ∈ polynomialBasisOpen R I d w T K.val
    rw [ht]
    trivial
  let l := IsOpenImmersion.lift i (𝟙 (Spec (.of T))) hr
  have hl : l ≫ i = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  have he : l ≫ polynomialBasisBaseChangeMorphism R I d w S J T = f := by
    rw [← cancel_mono (Scheme.Opens.ι (X := Spec (.of S))
      (polynomialBasisOpen R I d w S J)), Category.assoc, hf]
    rw [polynomialBasisBaseChangeMorphism, Scheme.Hom.resLE_comp_ι, ← Category.assoc]
    change (l ≫ i) ≫ _ = _
    rw [hl, Category.id_comp]
  rw [← he, Category.assoc, intrinsicChartMorphism_baseChange]
  change l ≫ intrinsicChartMorphism R I d w T K.val = _
  rw [intrinsicChartMorphism_global R I d w T K, ← Category.assoc]
  change (l ≫ i) ≫ _ = _
  rw [hl, Category.id_comp]

end FLT.Mazur.HilbertChart
