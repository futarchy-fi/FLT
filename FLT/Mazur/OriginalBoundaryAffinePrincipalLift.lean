/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.MonoComparisonOpenGluing
public import FLT.Mazur.OriginalBoundaryAssociatedPrincipalLift

/-!
# Full original arrows from associated rigidity on affine charts

The entire nonreduced coefficient scheme admits a unique original arrow.
Principal neighborhoods at associated primes construct local arrows; monomorphy proves
their overlap compatibility. Neither affineness nor compactness of the full
test, nor Noetherianity of its global sections, is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeScalarImageQuotient FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem affine_lift_endpoint_precompose {D A B U : Scheme.{0}}
    (p : D ⟶ A) (b : B ⟶ A) (u : U ⟶ B) [IsFinite (pullback.snd p b)] :
    IsFinite (pullback.snd p (u ≫ b)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd p b u]
  infer_instance

variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsAffine A] [Etale p]
  [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (J : A.IdealSheafData)
  (hJ : J.comap p = J.comap q)
local instance affineAssociatedPrincipalBoundary_affine : IsAffine J.subscheme :=
  isAffine_of_isAffineHom J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R₀" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R₀ Γ(J.subscheme, ⊤))
local notation "c" => originalBoundaryComparison p q J hJ
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "s" => RingHom.kerLift (FlatScalarFunctionPushout.scalarMap f)
attribute [local irreducible] scalarMorphism

include e

/-- Associated affine tests construct the full arrow, not just vanishing global equations. -/
theorem originalBoundary_unique_lift_of_affine_associated_principals
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : Set.range t ⊆ Set.range c)
    (hA : ∀ i, ∀ P ∈ associatedPrimes Γ(B.affineCover.X i, ⊤) Γ(B.affineCover.X i, ⊤),
      ∃ a : Γ(J.subscheme, ⊤),
        (let _ : Algebra (Scalars f) Γ(J.subscheme, ⊤) := (s).toAlgebra;
          Algebra.FormallyUnramified (Scalars f) (Localization.Away a)) ∧
        ((B.affineCover.f i ≫ t) ≫ pullback.snd f f).appTop a ∉ P) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  let _ := originalBoundaryComparison_mono e J hJ
  apply MonoComparisonOpenGluing.existsUnique_of_cover c t B.affineCover
  intro i
  let _ : IsAffine (B.affineCover.X i) := isAffine_Spec _
  let _ := isLocallyNoetherian_of_isOpenImmersion (B.affineCover.f i)
  let _ : IsNoetherian (B.affineCover.X i) := ⟨⟩
  let _ : IsFinite (pullback.snd p ((B.affineCover.f i ≫ t) ≫ x)) := by
    rw [Category.assoc]
    exact affine_lift_endpoint_precompose p (t ≫ x) (B.affineCover.f i)
  apply (originalBoundary_unique_lift_of_associated_principals e J hJ
    (B.affineCover.f i ≫ t) _ (hA i)).exists
  rintro _ ⟨u, rfl⟩
  exact h (Set.mem_range_self (B.affineCover.f i u))

end FLT.Mazur.EquivalenceRelationOrderedFrames
