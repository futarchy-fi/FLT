/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypePointedAbelFppfIso

/-!
# Effective fppf gluing of full acyclic Cartier ideals

Matching is expressed as equality of entire pulled-back ideal sheaves.
Sheaf descent constructs a unique actual full relative divisor on the test,
including its acyclic direct image. Covers and tests are unrestricted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.CartierAbel
open SchemePicard
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f]
  (e : Spec (.of R) ⟶ X) (he : e ≫ f = 𝟙 _)
  (T : Over (Spec (.of R))) (𝒰 : Scheme.Cover.{0} Scheme.fppfPrecoverage T.left)

include e he in
/-- Matching full acyclic divisors have a unique global full-ideal amalgamation. -/
theorem finiteTypeAcyclicDivisor_fppf_existsUnique
    (D : ∀ i, AcyclicRankOneRelativeDivisor
      (Limits.pullback.snd f (relativeCoverMember T 𝒰 i).hom))
    (hD : ∀ i j (V : Over (Spec (.of R)))
      (p : V ⟶ relativeCoverMember T 𝒰 i) (q : V ⟶ relativeCoverMember T 𝒰 j),
      p ≫ relativeCoverArrow T 𝒰 i = q ≫ relativeCoverArrow T 𝒰 j →
      (D i).val.val.comap (relativeTotalMap f p) =
        (D j).val.val.comap (relativeTotalMap f q)) :
    ∃! E : AcyclicRankOneRelativeDivisor (Limits.pullback.snd f T.hom),
      ∀ i, E.val.val.comap (relativeTotalMap f (relativeCoverArrow T 𝒰 i)) =
        (D i).val.val := by
  have h := relativeFppf_family_isSheafFor
    (finiteTypeAcyclicDivisorPresheaf_isSheaf f e he) T 𝒰
  rw [Presieve.isSheafFor_arrows_iff] at h
  have hm : Presieve.Arrows.Compatible (finiteTypeAcyclicDivisorPresheaf f)
      (relativeCoverArrow T 𝒰) D := by
    intro i j V p q hpq
    apply acyclicRankOneRelativeDivisor_ext
    change (finiteTypeAcyclicDivisorMap f p (D i)).val.val =
      (finiteTypeAcyclicDivisorMap f q (D j)).val.val
    rw [finiteTypeAcyclicDivisorMap_ideal, finiteTypeAcyclicDivisorMap_ideal]
    exact hD i j V p q hpq
  obtain ⟨E, hE, hu⟩ := h D hm
  refine ⟨E, fun i ↦ ?_, fun F hF ↦ hu F (fun i ↦ ?_)⟩
  · exact (finiteTypeAcyclicDivisorMap_ideal f _ E).symm.trans
      (congrArg (fun d ↦ d.val.val) (hE i))
  · apply acyclicRankOneRelativeDivisor_ext
    exact (finiteTypeAcyclicDivisorMap_ideal f _ F).trans (hF i)

end FLT.Mazur.CartierAbel
