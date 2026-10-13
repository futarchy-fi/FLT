/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteBranchInvariants
public import FLT.Mazur.SchemeRelationInvariantAffineUniversal

/-!
# The invariant affine candidate for the full original Hilbert relation

Construct its original base map and the canonical monomorphism from the full
relation to its scheme kernel pair. All affine-valued full-invariant maps
factor uniquely. Surjectivity and effectivity of this candidate are not claimed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "π" =>
  SchemeRelationInvariantSpectrum.projection (Over.Hom.left p) (Over.Hom.left q)

/-- The structural morphism satisfies the full original relation. -/
theorem invariantAffine_base_condition : (p).left ≫ A.hom = (q).left ≫ A.hom := by
  rw [Over.w, Over.w]

/-- The actual invariant affine candidate, retaining its original coefficient base. -/
def invariantAffineModel : Over (Spec (.of R)) :=
  Over.mk (SchemeRelationInvariantSpectrum.descend (p).left (q).left A.hom
    (invariantAffine_base_condition f hL d V c k))

instance invariantAffineModel_isAffine : IsAffine (invariantAffineModel f hL d V c k).left := by
  change IsAffine (Spec (.of (SchemeEffectiveEpiSections.compatibleFunctions (p).left (q).left)))
  infer_instance

/-- The parameter's actual relative morphism to the constructed affine candidate. -/
def invariantAffineProjection : A ⟶ invariantAffineModel f hL d V c k :=
  Over.homMk π (SchemeRelationInvariantSpectrum.projection_descend (p).left (q).left A.hom _)

/-- The relative projection coequalizes the entire original relation. -/
@[reassoc]
theorem invariantAffineProjection_condition :
    p ≫ invariantAffineProjection f hL d V c k =
      q ≫ invariantAffineProjection f hL d V c k := by
  apply Over.OverMorphism.ext
  exact SchemeRelationInvariantSpectrum.projection_condition (p).left (q).left

local notation "v" => invariantAffineProjection f hL d V c k

/-- The complete original relation maps to the candidate's actual scheme kernel pair. -/
def invariantAffineKernelMap : D ⟶ pullback v v :=
  pullback.lift p q (invariantAffineProjection_condition f hL d V c k)

/-- The comparison retains the full first original endpoint. -/
@[reassoc]
theorem invariantAffineKernelMap_fst :
    invariantAffineKernelMap f hL d V c k ≫ pullback.fst v v = p := pullback.lift_fst _ _ _

/-- The comparison retains the independent second original endpoint. -/
@[reassoc]
theorem invariantAffineKernelMap_snd :
    invariantAffineKernelMap f hL d V c k ≫ pullback.snd v v = q := pullback.lift_snd _ _ _

/-- No original arrows are lost in the comparison to the candidate kernel pair. -/
instance invariantAffineKernelMap_mono : Mono (invariantAffineKernelMap f hL d V c k) where
  right_cancellation a b h := by
    apply hom_ext f hL d V c k
    · simpa only [Category.assoc, invariantAffineKernelMap_fst] using
        congrArg (fun t ↦ t ≫ pullback.fst v v) h
    · simpa only [Category.assoc, invariantAffineKernelMap_snd] using
        congrArg (fun t ↦ t ≫ pullback.snd v v) h

/-- Every affine-valued full-invariant map factors uniquely through the actual candidate. -/
theorem invariantAffine_factor {Y : Scheme} [IsAffine Y] (g : A.left ⟶ Y)
    (hg : (p).left ≫ g = (q).left ≫ g) :
    ∃! h : (invariantAffineModel f hL d V c k).left ⟶ Y, (v).left ≫ h = g :=
  SchemeRelationInvariantSpectrum.existsUnique_affine_factor (p).left (q).left g hg

variable [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left]

/-- The actual constructed branch equations suffice for this exact affine universal property. -/
theorem invariantAffine_factor_of_branches {Y : Scheme} [IsAffine Y] (g : A.left ⟶ Y)
    (hg : ∀ r : (D).left,
      (EtaleFiniteBranchAtlas.original p r ≫ p).left ≫ g =
        (EtaleFiniteBranchAtlas.original p r ≫ q).left ≫ g) :
    ∃! h : (invariantAffineModel f hL d V c k).left ⟶ Y, (v).left ≫ h = g :=
  invariantAffine_factor f hL d V c k g
    ((finiteBranch_coequalizes_iff f hL d V c k g).mpr hg)

end FLT.Mazur.HilbertChart.AffineRestriction
