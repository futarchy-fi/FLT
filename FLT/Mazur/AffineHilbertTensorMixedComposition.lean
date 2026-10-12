/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTensorPullback

/-!
# A full mixed-chart composition atlas for the original relation

The two arrows and their composite may use independent tensor denominators.
Their simultaneous domains cover every original composable pair, and have
affine refinements. The three actual coefficient laws hold on each such domain.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation AffineProductTensorCoordinates
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
local notation "Z" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
/-- The algebra induced by the original source structural morphism. -/
local instance mixedSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original translation structural morphism. -/
local instance mixedTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom


namespace TensorChart
local notation "C" => composable f hL d V c k
local notation "a" => Over.Hom.left (pullback.fst q p)
local notation "b" => Over.Hom.left (pullback.snd q p)
local notation "m" =>
  Over.Hom.left (CategoryTheory.EquivalenceRelation.t (equivalence f hL d V c k))
variable (T S Q : TensorChart f hL d V c k)

/-- The simultaneous domain of two original chart arrows and their original composite. -/
def mixedDomain : (C).left.Opens :=
  ((a) ⁻¹ᵁ T.domain ⊓ (b) ⁻¹ᵁ S.domain) ⊓ (m) ⁻¹ᵁ Q.domain

/-- These simultaneous chart domains cover all composable pairs of the original relation. -/
theorem exists_mem_mixedDomain (x : (C).left) :
    ∃ T S Q : TensorChart f hL d V c k, x ∈ mixedDomain f hL d V c k T S Q := by
  obtain ⟨T, hT, _⟩ := exists_mem f hL d V c k ((a) x) ⊤ trivial
  obtain ⟨S, hS, _⟩ := exists_mem f hL d V c k ((b) x) ⊤ trivial
  obtain ⟨Q, hQ, _⟩ := exists_mem f hL d V c k ((m) x) ⊤ trivial
  exact ⟨T, S, Q, ⟨⟨hT, hS⟩, hQ⟩⟩

/-- Every mixed composition domain has actual affine refinements about all of its points. -/
theorem exists_mixed_affine (x : (C).left) (hx : x ∈ mixedDomain f hL d V c k T S Q)
    (W : (C).left.Opens) (hxW : x ∈ W) :
    ∃ B : (C).left.Opens, IsAffineOpen B ∧ x ∈ B ∧ B ≤ W ∧
      B ≤ mixedDomain f hL d V c k T S Q := by
  obtain ⟨B, hB, hxB, hBW⟩ := exists_composable_affine_neighborhood f hL d V c k
    (W ⊓ mixedDomain f hL d V c k T S Q) {x} (Set.finite_singleton x)
    (Set.singleton_subset_iff.mpr ⟨hxW, hx⟩)
  exact ⟨B, hB, hxB (Set.mem_singleton x), hBW.trans inf_le_left, hBW.trans inf_le_right⟩

/-- Every composable pair has an affine chart with three specified original localization targets. -/
theorem exists_mixed_affine_at (x : (C).left) (W : (C).left.Opens) (hxW : x ∈ W) :
    ∃ (T S Q : TensorChart f hL d V c k) (B : (C).left.Opens),
      IsAffineOpen B ∧ x ∈ B ∧ B ≤ W ∧ B ≤ mixedDomain f hL d V c k T S Q := by
  obtain ⟨T, S, Q, hx⟩ := exists_mem_mixedDomain f hL d V c k x
  obtain ⟨B, hB⟩ := exists_mixed_affine f hL d V c k T S Q x hx W hxW
  exact ⟨T, S, Q, B, hB⟩

variable (B : (composable f hL d V c k).left.Opens)
  (hB : B ≤ mixedDomain f hL d V c k T S Q)

/-- The first actual arrow into its independently chosen chart. -/
def mixedFirst : B.toScheme ⟶ T.domain.toScheme :=
  (a).resLE T.domain B (hB.trans (inf_le_left.trans inf_le_left))

/-- The second actual arrow into its independently chosen chart. -/
def mixedSecond : B.toScheme ⟶ S.domain.toScheme :=
  (b).resLE S.domain B (hB.trans (inf_le_left.trans inf_le_right))

/-- Actual composition into its independently chosen chart. -/
def mixedComposite : B.toScheme ⟶ Q.domain.toScheme :=
  (m).resLE Q.domain B (hB.trans inf_le_right)

/-- The first chart map retains its original arrow in the entire relation. -/
@[reassoc]
theorem mixedFirst_ι : mixedFirst f hL d V c k T S Q B hB ≫ T.domain.ι = B.ι ≫ a :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The second chart map retains its original arrow in the entire relation. -/
@[reassoc]
theorem mixedSecond_ι : mixedSecond f hL d V c k T S Q B hB ≫ S.domain.ι = B.ι ≫ b :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The composite chart map retains the full original composition morphism. -/
@[reassoc]
theorem mixedComposite_ι : mixedComposite f hL d V c k T S Q B hB ≫ Q.domain.ι = B.ι ≫ m :=
  Scheme.Hom.resLE_comp_ι _ _

/-- First-endpoint composition holds across arbitrary, independently localized charts. -/
theorem mixed_source (z : Γ(A.left, ⊤)) :
    localizedEvaluation f hL d V c k Q.denominator Q.domain Q.image_eq
      (mixedComposite f hL d V c k T S Q B hB)
      (localizedSourceMap f hL d V c k Q.denominator Q.domain Q.image_eq z) =
    localizedEvaluation f hL d V c k T.denominator T.domain T.image_eq
      (mixedFirst f hL d V c k T S Q B hB)
      (localizedSourceMap f hL d V c k T.denominator T.domain T.image_eq z) := by
  rw [localizedEvaluation_source, localizedEvaluation_source,
    mixedComposite_ι_assoc, mixedFirst_ι_assoc]
  exact congrArg (fun g ↦ (B.ι ≫ g).appTop z)
    (congrArg Over.Hom.left (equivalence f hL d V c k).transitivity₁)

/-- The intermediate endpoint agrees across the independent first and second chart rings. -/
theorem mixed_middle (z : Γ(A.left, ⊤)) :
    localizedEvaluation f hL d V c k T.denominator T.domain T.image_eq
      (mixedFirst f hL d V c k T S Q B hB)
      (localizedTestMap f hL d V c k T.denominator T.domain T.image_eq z) =
    localizedEvaluation f hL d V c k S.denominator S.domain S.image_eq
      (mixedSecond f hL d V c k T S Q B hB)
      (localizedSourceMap f hL d V c k S.denominator S.domain S.image_eq z) := by
  rw [localizedEvaluation_test, localizedEvaluation_source,
    mixedFirst_ι_assoc, mixedSecond_ι_assoc]
  exact congrArg (fun g ↦ (B.ι ≫ g).appTop z)
    (congrArg Over.Hom.left (pullback.condition (f := q) (g := p)))

/-- Second-endpoint composition holds on the full mixed composition atlas. -/
theorem mixed_test (z : Γ(A.left, ⊤)) :
    localizedEvaluation f hL d V c k Q.denominator Q.domain Q.image_eq
      (mixedComposite f hL d V c k T S Q B hB)
      (localizedTestMap f hL d V c k Q.denominator Q.domain Q.image_eq z) =
    localizedEvaluation f hL d V c k S.denominator S.domain S.image_eq
      (mixedSecond f hL d V c k T S Q B hB)
      (localizedTestMap f hL d V c k S.denominator S.domain S.image_eq z) := by
  rw [localizedEvaluation_test, localizedEvaluation_test,
    mixedComposite_ι_assoc, mixedSecond_ι_assoc]
  exact congrArg (fun g ↦ (B.ι ≫ g).appTop z)
    (congrArg Over.Hom.left (equivalence f hL d V c k).transitivity₂)

/-- The first endpoint law also holds globally on the entire original composable-pair scheme. -/
theorem matching_composition_source (z : Γ(A.left, ⊤)) :
    matchingPullback f hL d V c k (m) (matchingSource f hL d V c k z) =
      matchingPullback f hL d V c k (a) (matchingSource f hL d V c k z) := by
  rw [matchingPullback_source, matchingPullback_source]
  exact congrArg (fun g : (C).left ⟶ A.left ↦ g.appTop z)
    (congrArg Over.Hom.left (equivalence f hL d V c k).transitivity₁)

/-- The matching families agree at the intermediate endpoint on the full composable scheme. -/
theorem matching_composition_middle (z : Γ(A.left, ⊤)) :
    matchingPullback f hL d V c k (a) (matchingTest f hL d V c k z) =
      matchingPullback f hL d V c k (b) (matchingSource f hL d V c k z) := by
  rw [matchingPullback_test, matchingPullback_source]
  exact congrArg (fun g : (C).left ⟶ A.left ↦ g.appTop z)
    (congrArg Over.Hom.left (pullback.condition (f := q) (g := p)))

/-- The second endpoint law holds globally on the entire original composable-pair scheme. -/
theorem matching_composition_test (z : Γ(A.left, ⊤)) :
    matchingPullback f hL d V c k (m) (matchingTest f hL d V c k z) =
      matchingPullback f hL d V c k (b) (matchingTest f hL d V c k z) := by
  rw [matchingPullback_test, matchingPullback_test]
  exact congrArg (fun g : (C).left ⟶ A.left ↦ g.appTop z)
    (congrArg Over.Hom.left (equivalence f hL d V c k).transitivity₂)

end TensorChart
end FLT.Mazur.HilbertChart.AffineRestriction
