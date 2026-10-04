/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GeometricHopfLocalizedKernel
public import FLT.Mathlib.RingTheory.MvPolynomial.CoefficientPresentation
public import FLT.Mathlib.RingTheory.MvPolynomial.GeometricRegularDescent

/-! # Original fibre relations from a geometric Hopf comparison -/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace HopfAlgebra

open FiniteAlgebra MvPolynomial

variable {k K A H : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
  [CommRing A] [Algebra k A] [CommRing H] [HopfAlgebra K H]
  [IsArtinianRing H] [Module.Finite K H]
  (p : ℕ) [Fact p.Prime] [CharP K p]

include p

/-- A geometric Hopf comparison constructs regular relations for the original fibre
presentation at each contracted geometric point, including non-rational residue points. -/
theorem exists_original_fibre_regular_relations {n : ℕ}
    (f : MvPolynomial (Fin n) k →ₐ[k] A) (hf : Function.Surjective f)
    (e : K ⊗[k] A ≃ₐ[K] H) (ε : H →ₐ[K] K) :
    let a := fun i ↦ ε (e (1 ⊗ₜ f (X i)))
    ∃ rs : List (GeometricPointSource k K a), rs.length = n ∧
      Ideal.ofList rs = (RingHom.ker f).map (algebraMap _ (GeometricPointSource k K a)) ∧
      RingTheory.Sequence.IsRegular (GeometricPointSource k K a) rs := by
  let g := e.toAlgHom.comp (coefficientPresentation K f)
  have hg : Function.Surjective g := e.surjective.comp (coefficientPresentation_surjective K f hf)
  have hk : RingHom.ker g = (RingHom.ker f).map (map (algebraMap k K)) := by
    rw [← ker_coefficientPresentation K f hf]
    ext q
    change e (coefficientPresentation K f q) = 0 ↔ coefficientPresentation K f q = 0
    exact map_eq_zero_iff e e.injective
  let a := fun i ↦ ε (g (X i))
  obtain ⟨v, eqv, hv⟩ := exists_geometric_point_kernel p ε g hg
  let I := (RingHom.ker f).map (algebraMap _ (GeometricPointSource k K a))
  have hI : I.map (geometricPointLocalizationMap k K a) =
      (RingHom.ker g).map (algebraMap _ (Localization.AtPrime (rationalPointIdeal a))) := by
    rw [hk]
    exact map_ideal_geometricPointLocalization k K a (RingHom.ker f)
  have : IsArtinianRing (Localization.AtPrime (rationalPointIdeal a) ⧸
      I.map (geometricPointLocalizationMap k K a)) := by
    rw [hI]
    exact eqv.symm.toRingEquiv.isArtinianRing
  have : Nontrivial (Localization.AtPrime (rationalPointIdeal a) ⧸
      I.map (geometricPointLocalizationMap k K a)) := by
    rw [hI]
    exact eqv.surjective.nontrivial
  have h := exists_regular_relations_at_geometricPoint a I v (hI.trans hv)
  have ha : a = (fun i ↦ ε (e (1 ⊗ₜ f (X i)))) := by
    funext i
    simp [a, g]
  change ∃ rs : List (GeometricPointSource k K a), rs.length = n ∧
    Ideal.ofList rs = (RingHom.ker f).map (algebraMap _ (GeometricPointSource k K a)) ∧
    RingTheory.Sequence.IsRegular (GeometricPointSource k K a) rs at h
  exact ha ▸ h

end HopfAlgebra
