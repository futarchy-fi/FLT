/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertLocalizedCoefficients

/-!
# The actual counit on a principal tensor relation chart

The identity section factors through a relation chart on its exact inverse
image in the original source. The two localized endpoint maps both evaluate
to restriction on this domain. Finite source sets whose identities lie in
the chart have a single principal affine counit neighborhood.
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
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "r" =>
  Over.Hom.left (ReflexiveRelation.r
    (EquivalenceRelation.toReflexiveRelation (equivalence f hL d V c k)))
variable (U : (relation f hL d V c k).left.Opens)

/-- The exact source domain where the original identity arrow lies in the chosen chart. -/
def identityDomain : A.left.Opens := (r) ⁻¹ᵁ U

/-- The original identity arrow, restricted to its exact chart domain. -/
def identityChartMap : (identityDomain f hL d V c k U).toScheme ⟶ U.toScheme := (r) ∣_ U

/-- The local identity is the original identity section after the chart inclusion. -/
@[reassoc]
theorem identityChartMap_ι : identityChartMap f hL d V c k U ≫ U.ι =
    (identityDomain f hL d V c k U).ι ≫ r := morphismRestrict_ι _ _

variable [IsAffine A.left]

/-- A whole finite set of source points has one principal affine counit neighborhood. -/
theorem exists_identity_principal_neighborhood (s : Set A.left) (hs : s.Finite)
    (hsU : (r) '' s ⊆ U) (W : A.left.Opens) (hsW : s ⊆ W) :
    ∃ a : Γ(A.left, ⊤), s ⊆ A.left.basicOpen a ∧
      A.left.basicOpen a ≤ W ∧ A.left.basicOpen a ≤ identityDomain f hL d V c k U := by
  obtain ⟨a, ha, haW⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (W ⊓ identityDomain f hL d V c k U) s hs
    (fun x hx ↦ ⟨hsW hx, hsU (Set.mem_image_of_mem r hx)⟩)
  exact ⟨a, ha, haW.trans inf_le_left, haW.trans inf_le_right⟩

variable [IsAffine V.left] [IsOpenImmersion k.left]
/-- The algebra induced by the original structural morphism. -/
local instance counitSourceAlgebra : Algebra R Γ(A.left, ⊤) :=
  affineBaseSectionAlgebra A.hom
/-- The algebra induced by the original structural morphism. -/
local instance counitTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable (t : Γ(A.left, ⊤) ⊗[R] Γ(V.left, ⊤))
  (hU : (toEnvelope f hL d V c k).left ''ᵁ U =
    (prod A V).left.basicOpen ((tensorIso A V).hom t))

/-- The actual local counit is a ring homomorphism out of the literal tensor localization. -/
def localizedCounit : Localization.Away t →+*
    Γ((identityDomain f hL d V c k U).toScheme, ⊤) :=
  localizedEvaluation f hL d V c k t U hU (identityChartMap f hL d V c k U)

/-- The first localized coefficient map has the original restriction as its local counit. -/
theorem localizedCounit_source (a : Γ(A.left, ⊤)) :
    localizedCounit f hL d V c k U t hU (localizedSourceMap f hL d V c k t U hU a) =
      (identityDomain f hL d V c k U).ι.appTop a := by
  rw [localizedCounit, localizedEvaluation_source, identityChartMap_ι_assoc]
  have h := congrArg Over.Hom.left (equivalence f hL d V c k).reflexivity₁
  change (r) ≫ (p).left = 𝟙 A.left at h
  rw [h, Category.comp_id]

/-- The second localized coefficient map has the same original restriction as its local counit. -/
theorem localizedCounit_test (a : Γ(A.left, ⊤)) :
    localizedCounit f hL d V c k U t hU (localizedTestMap f hL d V c k t U hU a) =
      (identityDomain f hL d V c k U).ι.appTop a := by
  rw [localizedCounit, localizedEvaluation_test, identityChartMap_ι_assoc]
  have h := congrArg Over.Hom.left (equivalence f hL d V c k).reflexivity₂
  change (r) ≫ (q).left = 𝟙 A.left at h
  rw [h, Category.comp_id]

end FLT.Mazur.HilbertChart.AffineRestriction
