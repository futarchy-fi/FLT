/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertClosedPatchSource

/-!
# Compatible refinements of unreduced closed finite-model patches

An inclusion of arbitrary ideals induces the actual closed target map and its
complete source base change. Both original source and coefficient maps commute.
Thus infinitesimal thickenings and their reductions remain compatible, rather
than being replaced by unrelated reduced models.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "Q" => finiteKernelModel f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k
variable (r : Γ((finiteKernelModel f hL d V c k).left, ⊤))
local notation "U" => Scheme.basicOpen (Over.left Q) r
local notation "g" => finiteModelPrincipalProjection f hL d V c k r
variable {J K : Ideal Γ(((finiteKernelModel f hL d V c k).left.basicOpen r).toScheme, ⊤)}
  (hJK : J ≤ K)
local notation "iJ" => finiteModelStratumMap f hL d V c k r J
local notation "iK" => finiteModelStratumMap f hL d V c k r K

/-- The actual map of quotient rings determines the closed target refinement. -/
def finiteModelClosedTargetRefinement :
    Spec (.of (Γ((U).toScheme, ⊤) ⧸ K)) ⟶ Spec (.of (Γ((U).toScheme, ⊤) ⧸ J)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJK))

local notation "t" => finiteModelClosedTargetRefinement f hL d V c k r hJK

/-- The refinement retains the original principal target and all its coefficients. -/
@[reassoc]
theorem finiteModelClosedTargetRefinement_patch : t ≫ iJ = iK := by
  dsimp only [finiteModelClosedTargetRefinement, finiteModelStratumMap]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- Every refinement is the actual quotient closed immersion. -/
instance finiteModelClosedTargetRefinement_isClosedImmersion : IsClosedImmersion t := by
  apply IsClosedImmersion.spec_of_surjective
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk J y, rfl⟩

/-- The entire source over the smaller closed patch maps to the source over the larger one. -/
def finiteModelClosedSourceRefinement : finiteModelClosedPatchSource f hL d V c k r K ⟶
    finiteModelClosedPatchSource f hL d V c k r J :=
  Over.homMk (pullback.lift (pullback.fst g iK) (pullback.snd g iK ≫ t) (by
    rw [Category.assoc, finiteModelClosedTargetRefinement_patch, pullback.condition])) (by
      change pullback.lift _ _ _ ≫ pullback.fst g iJ ≫
        ((v).left ⁻¹ᵁ U).ι ≫ A.hom = _
      rw [pullback.lift_fst_assoc]
      rfl)

local notation "s" => finiteModelClosedSourceRefinement f hL d V c k r hJK

/-- The source comparison retains the complete original principal-source coordinate. -/
@[reassoc]
theorem finiteModelClosedSourceRefinement_fst :
    (s).left ≫ pullback.fst g iJ = pullback.fst g iK := pullback.lift_fst _ _ _

/-- Its target coordinate is exactly the original quotient-ring refinement. -/
@[reassoc]
theorem finiteModelClosedSourceRefinement_snd :
    (s).left ≫ pullback.snd g iJ = pullback.snd g iK ≫ t := pullback.lift_snd _ _ _

/-- The comparison retains the original source map, not merely its points. -/
@[reassoc]
theorem finiteModelClosedSourceRefinement_original :
    s ≫ finiteModelClosedPatchSourceMap f hL d V c k r J =
      finiteModelClosedPatchSourceMap f hL d V c k r K := by
  apply Over.OverMorphism.ext
  change (s).left ≫ pullback.fst g iJ ≫ ((v).left ⁻¹ᵁ U).ι = _
  rw [finiteModelClosedSourceRefinement_fst_assoc]
  rfl

/-- The whole source comparison is the actual closed target base change. -/
theorem finiteModelClosedSourceRefinement_isPullback :
    IsPullback (s).left (pullback.snd g iK) (pullback.snd g iJ) t := by
  have hh : IsPullback ((s).left ≫ pullback.fst g iJ) (pullback.snd g iK) g
      (t ≫ iJ) := by
    rw [finiteModelClosedSourceRefinement_fst, finiteModelClosedTargetRefinement_patch]
    exact IsPullback.of_hasPullback g iK
  exact hh.of_right (finiteModelClosedSourceRefinement_snd f hL d V c k r hJK)
    (IsPullback.of_hasPullback g iJ)

/-- Nilpotent or residual closed refinements are closed immersions of entire source schemes. -/
instance finiteModelClosedSourceRefinement_isClosedImmersion : IsClosedImmersion (s).left :=
  MorphismProperty.of_isPullback
    (finiteModelClosedSourceRefinement_isPullback f hL d V c k r hJK).flip inferInstance

end FLT.Mazur.HilbertChart.AffineRestriction
