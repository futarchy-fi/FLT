/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechGenericEvaluation
public import FLT.Mazur.ProperFiberEvaluationLocus

/-!
# Actual connected fibers and tensor evaluation on a generic open

The residue-field map of a point in a principal open factors through that open.
For a proper smooth pointed family, the actual connected-fiber locus therefore
agrees there with tensor evaluation using actual residue-spectrum coefficients.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechCartesian
open ArtinianRelativeSectionCriterion Approximation FCurve

variable {X S : Scheme.{0}} [IsAffine S]
  [IsNoetherianRing Γ(S, ⊤)] [IsDomain Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Smooth f] [X.IsSeparated]
  {ι : Type} [LinearOrder ι] [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
  (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

include hU hCover in
/-- The actual smooth connected-fiber locus has a tensor evaluation criterion on one open. -/
theorem exists_generic_connectedFiber_iff_tensor :
    ∃ r : Γ(S, ⊤), r ≠ 0 ∧ ∀ (b : S), b ∈ S.basicOpen r →
      let _ : Algebra Γ(S, ⊤) Γ(Spec (S.residueField b), ⊤) :=
        (S.fromSpecResidueField b).appTop.hom.toAlgebra
      (b ∈ geometricallyConnectedLocus f ↔
        Function.Injective ((evaluation f σ hσ).lTensor Γ(Spec (S.residueField b), ⊤))) := by
  obtain ⟨r, hr, he⟩ := exists_generic_sectionEvaluation_injective_iff_tensor f U hU hCover σ hσ
  refine ⟨r, hr, ?_⟩
  intro b hb
  dsimp only
  let _ : Algebra Γ(S, ⊤) Γ(Spec (S.residueField b), ⊤) :=
    (S.fromSpecResidueField b).appTop.hom.toAlgebra
  have hrange : Set.range (S.fromSpecResidueField b) ⊆ Set.range (S.basicOpen r).ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    exact Set.singleton_subset_iff.mpr hb
  let t := IsOpenImmersion.lift (S.basicOpen r).ι (S.fromSpecResidueField b) hrange
  have ht : t ≫ (S.basicOpen r).ι = S.fromSpecResidueField b :=
    IsOpenImmersion.lift_fac _ _ hrange
  let τ := residueFiberSection f σ hσ b
  have hq : τ ≫ f.fiberToSpecResidueField b = 𝟙 _ :=
    residueFiberSection_projection f σ hσ b
  have hp : τ ≫ f.fiberι b = S.fromSpecResidueField b ≫ σ :=
    pullback.lift_fst _ _ _
  have hc := he (IsPullback.of_hasPullback f (S.fromSpecResidueField b)) t ht τ hq hp
  rw [geometricallyConnectedLocus_eq_evaluation_locus_of_smooth f σ hσ]
  dsimp only at hc
  let e := (Scheme.ΓSpecIso (S.residueField b)).commRingCatIsoToRingEquiv
  change Function.Injective (fun x ↦ e (τ.appTop x)) ↔ _
  refine Iff.trans ?_ hc
  constructor
  · intro hi x y hxy
    exact hi (congrArg e hxy)
  · intro hi x y hxy
    exact hi (e.injective hxy)

end FLT.Mazur.IncreasingCechCartesian
