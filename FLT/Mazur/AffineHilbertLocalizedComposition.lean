/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertCompositionCharts
public import FLT.Mazur.AffineHilbertLocalizedCoefficients

/-!
# Local multiplicative composition laws for the original Picard relation

On the constructed composition domains all three arrows factor through the
same literal tensor-localization chart. Evaluating either endpoint map proves
the two outer coefficient laws and equality at the intermediate endpoint.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation AffineProductTensorCoordinates
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "Z" => relation f hL d V c k
local notation "C" => composable f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "a" => Over.Hom.left (pullback.fst q p)
local notation "b" => Over.Hom.left (pullback.snd q p)
local notation "m" =>
  Over.Hom.left (CategoryTheory.EquivalenceRelation.t (equivalence f hL d V c k))
variable (U : (relation f hL d V c k).left.Opens) (B : (composable f hL d V c k).left.Opens)
  (hB : B ≤ compositionDomain f hL d V c k U)

/-- The first original arrow factors through the chosen relation chart. -/
def compositionChartFirst : B.toScheme ⟶ U.toScheme :=
  (C).left.homOfLE (hB.trans (inf_le_left.trans inf_le_left)) ≫ (a) ∣_ U

/-- The second original arrow factors through the same relation chart. -/
def compositionChartSecond : B.toScheme ⟶ U.toScheme :=
  (C).left.homOfLE (hB.trans (inf_le_left.trans inf_le_right)) ≫ (b) ∣_ U

/-- The actual composite factors through the same relation chart. -/
def compositionChartComposite : B.toScheme ⟶ U.toScheme :=
  (C).left.homOfLE (hB.trans inf_le_right) ≫ (m) ∣_ U

/-- The first chart map retains its original scheme morphism. -/
@[reassoc]
theorem compositionChartFirst_ι :
    compositionChartFirst f hL d V c k U B hB ≫ U.ι = B.ι ≫ a := by
  rw [compositionChartFirst, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]

/-- The second chart map retains its original scheme morphism. -/
@[reassoc]
theorem compositionChartSecond_ι :
    compositionChartSecond f hL d V c k U B hB ≫ U.ι = B.ι ≫ b := by
  rw [compositionChartSecond, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]

/-- The composite chart map retains actual composition in the full original relation. -/
@[reassoc]
theorem compositionChartComposite_ι :
    compositionChartComposite f hL d V c k U B hB ≫ U.ι = B.ι ≫ m := by
  rw [compositionChartComposite, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]

variable [IsAffine V.left] [IsAffine A.left] [IsOpenImmersion k.left]
/-- The algebra induced by the original structural morphism. -/
local instance localCompositionSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original structural morphism. -/
local instance localCompositionTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤))
  (hU : (toEnvelope f hL d V c k).left ''ᵁ U =
    (prod A V).left.basicOpen ((tensorIso A V).hom t))

/-- The first endpoint of the composite has the first arrow's actual localized coefficients. -/
theorem localizedComposition_source (z : Γ(A.left, ⊤)) :
    localizedEvaluation f hL d V c k t U hU
      (compositionChartComposite f hL d V c k U B hB)
      (localizedSourceMap f hL d V c k t U hU z) =
    localizedEvaluation f hL d V c k t U hU
      (compositionChartFirst f hL d V c k U B hB)
      (localizedSourceMap f hL d V c k t U hU z) := by
  rw [localizedEvaluation_source, localizedEvaluation_source,
    compositionChartComposite_ι_assoc, compositionChartFirst_ι_assoc]
  have h := congrArg Over.Hom.left (equivalence f hL d V c k).transitivity₁
  exact congrArg (fun g ↦ (B.ι ≫ g).appTop z) h

/-- The intermediate localized coefficient agrees along the two composable original arrows. -/
theorem localizedComposition_middle (z : Γ(A.left, ⊤)) :
    localizedEvaluation f hL d V c k t U hU
      (compositionChartFirst f hL d V c k U B hB)
      (localizedTestMap f hL d V c k t U hU z) =
    localizedEvaluation f hL d V c k t U hU
      (compositionChartSecond f hL d V c k U B hB)
      (localizedSourceMap f hL d V c k t U hU z) := by
  rw [localizedEvaluation_test, localizedEvaluation_source,
    compositionChartFirst_ι_assoc, compositionChartSecond_ι_assoc]
  have h : (a) ≫ (q).left = (b) ≫ (p).left :=
    congrArg Over.Hom.left (pullback.condition (f := q) (g := p))
  exact congrArg (fun g ↦ (B.ι ≫ g).appTop z) h

/-- The second endpoint of the composite has the second arrow's actual localized coefficients. -/
theorem localizedComposition_test (z : Γ(A.left, ⊤)) :
    localizedEvaluation f hL d V c k t U hU
      (compositionChartComposite f hL d V c k U B hB)
      (localizedTestMap f hL d V c k t U hU z) =
    localizedEvaluation f hL d V c k t U hU
      (compositionChartSecond f hL d V c k U B hB)
      (localizedTestMap f hL d V c k t U hU z) := by
  rw [localizedEvaluation_test, localizedEvaluation_test,
    compositionChartComposite_ι_assoc, compositionChartSecond_ι_assoc]
  have h := congrArg Over.Hom.left (equivalence f hL d V c k).transitivity₂
  exact congrArg (fun g ↦ (B.ι ≫ g).appTop z) h

end FLT.Mazur.HilbertChart.AffineRestriction
