/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation
public import FLT.Mazur.EtaleFiniteBranchSubcover
public import FLT.Mazur.SchemeFppfCoverInvariantFunctions

/-!
# A finite affine branch cover of the full selected Hilbert relation

Derived Noetherianity selects finitely many original branches covering the
entire relation. Both endpoint coefficient maps remain finitely presented,
and all full invariant equations are detected on this finite family.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

/-- Finitely many actual affine branches cover the entire original relation. -/
def finiteFullBranchCover :
    Scheme.Cover.{0} Scheme.fppfPrecoverage (relation f hL d V c k).left :=
  EtaleFiniteBranchAtlas.finiteFppfCover p

local notation "C" => finiteFullBranchCover f hL d V c k

instance finiteFullBranchCover_finite : Finite (C).I₀ :=
  inferInstanceAs (Finite (EtaleFiniteBranchAtlas.finiteFppfCover p).I₀)

instance finiteFullBranchCover_isAffine (i : (C).I₀) : IsAffine ((C).X i) :=
  inferInstanceAs (IsAffine ((EtaleFiniteBranchAtlas.finiteFppfCover p).X i))

/-- The selected source maps retain their original étale geometry. -/
instance finiteFullBranchCover_etale (i : (C).I₀) : Etale ((C).f i) :=
  inferInstanceAs (Etale (EtaleFiniteBranchAtlas.original p i.val).left)

/-- Both original endpoints give finitely presented maps on each selected coefficient ring. -/
theorem finiteFullBranchCover_endpoint_finitePresentation (i : (C).I₀) :
    ((C).f i ≫ (p).left).appTop.hom.FinitePresentation ∧
      ((C).f i ≫ (q).left).appTop.hom.FinitePresentation :=
  ⟨((C).f i ≫ (p).left).finitePresentation_appTop,
    ((C).f i ≫ (q).left).finitePresentation_appTop⟩

/-- The finitely many branches assemble to one actual affine scheme. -/
abbrev finiteFullBranchSource : Scheme := SchemeFppfFamily.total C

instance finiteFullBranchSource_isAffine : IsAffine (finiteFullBranchSource f hL d V c k) := by
  change IsAffine (∐ (C).X)
  infer_instance

/-- A single actual affine fppf presentation of the entire original relation. -/
def finiteFullBranchProjection : finiteFullBranchSource f hL d V c k ⟶
    (relation f hL d V c k).left := SchemeFppfFamily.projection C

instance finiteFullBranchProjection_etale : Etale (finiteFullBranchProjection f hL d V c k) :=
  IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ ↦ inferInstance)

instance finiteFullBranchProjection_surjective :
    Surjective (finiteFullBranchProjection f hL d V c k) :=
  SchemeFppfFamily.projection_surjective C

instance finiteFullBranchProjection_quasiCompact :
    QuasiCompact (finiteFullBranchProjection f hL d V c k) := by
  unfold finiteFullBranchProjection
  infer_instance

/-- Both independent endpoint algebras on the affine presentation are finitely presented. -/
theorem finiteFullBranchProjection_endpoint_finitePresentation :
    (finiteFullBranchProjection f hL d V c k ≫ (p).left).appTop.hom.FinitePresentation ∧
      (finiteFullBranchProjection f hL d V c k ≫ (q).left).appTop.hom.FinitePresentation :=
  ⟨(finiteFullBranchProjection f hL d V c k ≫ (p).left).finitePresentation_appTop,
    (finiteFullBranchProjection f hL d V c k ≫ (q).left).finitePresentation_appTop⟩

/-- Pullback along the affine presentation detects the full original invariant ring exactly. -/
theorem finiteFullBranchProjection_invariants :
    compatibleFunctions (finiteFullBranchProjection f hL d V c k ≫ (p).left)
      (finiteFullBranchProjection f hL d V c k ≫ (q).left) =
        compatibleFunctions (p).left (q).left := by
  ext a
  change (finiteFullBranchProjection f hL d V c k ≫ (p).left).appTop a =
      (finiteFullBranchProjection f hL d V c k ≫ (q).left).appTop a ↔ _
  simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
  exact (appTop_injective (finiteFullBranchProjection f hL d V c k)).eq_iff

/-- The original full invariant equations are exactly the finitely many branch equations. -/
theorem finiteFullBranchCover_invariants (a : Γ(A.left, ⊤)) :
    a ∈ compatibleFunctions (p).left (q).left ↔
      ∀ i : (C).I₀, a ∈ compatibleFunctions ((C).f i ≫ (p).left) ((C).f i ≫ (q).left) :=
  SchemeFppfFamily.mem_compatibleFunctions_iff C (p).left (q).left a

/-- No relation arrow is lost: complete scheme coequalization is detected by the finite cover. -/
theorem finiteFullBranchCover_coequalizes {Y : Scheme} (g : A.left ⟶ Y) :
    (p).left ≫ g = (q).left ≫ g ↔
      ∀ i : (C).I₀, (C).f i ≫ (p).left ≫ g = (C).f i ≫ (q).left ≫ g :=
  SchemeFppfFamily.coequalizes_iff C (p).left (q).left g

end FLT.Mazur.HilbertChart.AffineRestriction
