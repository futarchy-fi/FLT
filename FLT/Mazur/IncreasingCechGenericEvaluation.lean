/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechEvaluationComparison

/-!
# Generic geometric evaluation comparison

One nonzero principal open identifies injectivity of actual section evaluation
with injectivity of tensor evaluation for every affine cartesian base change
factoring through it. No kernel or localization-action hypothesis remains.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechCartesian
open PrincipalOpenSectionAlgebra ArtinianRelativeSectionCriterion

variable {X S : Scheme.{0}} [IsAffine S]
  [IsNoetherianRing Γ(S, ⊤)] [IsDomain Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
  (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

include hU hCover in
/-- All actual cartesian sections on one principal open satisfy the tensor evaluation criterion. -/
theorem exists_generic_sectionEvaluation_injective_iff_tensor :
    ∃ r : Γ(S, ⊤), r ≠ 0 ∧ ∀ {P T : Scheme.{0}}
      {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
      (_h : IsPullback p q f g) [IsAffine T]
      (t : T ⟶ (S.basicOpen r).toScheme) (_ht : t ≫ (S.basicOpen r).ι = g)
      (τ : T ⟶ P) (_hq : τ ≫ q = 𝟙 T) (_hp : τ ≫ p = g ≫ σ),
      let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
      Function.Injective τ.appTop ↔
        Function.Injective ((evaluation f σ hσ).lTensor Γ(T, ⊤)) := by
  obtain ⟨r, hr, hc⟩ := exists_affine_generic_tensorKer_bijective f U hU hCover
  refine ⟨r, hr, ?_⟩
  intro P T p q g h _ t ht τ hq hp
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  let hu := isUnit_of_factor g r t ht
  let _ := sectionAlgebra g r hu
  let _ := sectionAlgebra_tower g r hu
  apply sectionEvaluation_injective_iff_tensor h U hU hCover (Submonoid.powers r) σ hσ τ hq hp
  apply localizedSectionsComparison_bijective
  exact hc 0 Γ(T, ⊤)

end FLT.Mazur.IncreasingCechCartesian
