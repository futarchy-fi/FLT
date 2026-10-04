/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LiftedSquareChartCover
public import FLT.Mathlib.RingTheory.MvPolynomial.PrincipalSquarePresentation

/-! # Construct a faithfully flat lift of the original principal square chart cover -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.Presentation

variable {B C A ι : Type*} [CommRing B] [CommRing C] [CommRing A]
  [Algebra B C] [Algebra C A] [Algebra B A] [IsScalarTower B C A]
  [Module.Finite C A] [Module.FaithfullyFlat C A] [Finite ι] {d : ℕ}

/-- A finite square principal cover of a finite faithfully flat algebra lifts through
any nilpotent coefficient surjection. Both flatness and faithful covering are proved,
and each reduced lifted chart is identified with the specified original principal chart. -/
theorem exists_faithfullyFlat_liftedPrincipalCover
    (f : MvPolynomial (Fin d) C →ₐ[C] A) (hf : Function.Surjective f)
    (a : ι → MvPolynomial (Fin d) C) (rs : ι → List (MvPolynomial (Fin d) C))
    (hlen : ∀ i, (rs i).length = d)
    (hgen : ∀ i, Ideal.ofList ((rs i).map (algebraMap _ (Localization.Away (a i)))) =
      (RingHom.ker f).map (algebraMap _ (Localization.Away (a i))))
    (hspan : Ideal.span (Set.range fun i ↦ f (a i)) = ⊤)
    (hq : Function.Surjective (algebraMap B C)) {m : ℕ}
    (hn : RingHom.ker (algebraMap B C) ^ m = ⊥) :
    ∃ (P : ∀ i, Presentation C (Localization.Away (f (a i)))
          (Fin (d + 1)) (Fin (d + 1)))
      (g : ι → Fin (d + 1) → MvPolynomial (Fin (d + 1)) B)
      (_hg : ∀ i j, MvPolynomial.map (algebraMap B C) (g i j) = (P i).relation j),
      Module.FaithfullyFlat B
        (∀ i, MvPolynomial (Fin (d + 1)) B ⧸ Ideal.span (Set.range (g i))) ∧
      ∀ i, Nonempty (((MvPolynomial (Fin (d + 1)) B ⧸ Ideal.span (Set.range (g i)))
        ⊗[B] C) ≃ₐ[B] Localization.Away (f (a i))) := by
  classical
  let P i := Classical.choice (MvPolynomial.exists_principal_square_presentation f hf
    (a i) (rs i) (hlen i) (hgen i))
  choose g hg using fun i j ↦ MvPolynomial.map_surjective (algebraMap B C) hq ((P i).relation j)
  refine ⟨P, g, hg, ?_, fun i ↦ ⟨(P i).liftedPresentationBaseChangeEquiv (g i) (hg i) hq⟩⟩
  exact faithfullyFlat_liftedSquareChartCover (fun i ↦ Localization.Away (f (a i)))
    (fun _ ↦ d + 1) P g hg hq hn (PrimeSpectrum.localization_charts_cover _ hspan)

end Algebra.Presentation
