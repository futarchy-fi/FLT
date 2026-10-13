/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertNoetherianRelation
public import FLT.Mazur.AffineHilbertInvariantAffineModel
public import FLT.Mazur.SchemeRelationPrincipalSpectrum
public import FLT.Mazur.SchemeRelationPrincipalTensorSections

/-!
# Geometric principal invariants of the original Hilbert relation

On a Noetherian affine parameter source, every original invariant principal
localization is the invariant ring of the full restricted relation. Its
candidate is an actual open of the original invariant affine candidate, and
the source projection square commutes. Proper-family hypotheses are retained.
No claim of fppf projection or full kernel-pair isomorphism is made.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
open SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] [IsLocallyNoetherian A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "Rel" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local instance : CompactSpace (Rel).left := relation_compactSpace f hL d V c k
local instance : QuasiSeparatedSpace (Rel).left := relation_quasiSeparatedSpace f hL d V c k
variable (s : compatibleFunctions
  (FLT.Mazur.HilbertChart.AffineRestriction.fst f hL d V c k).left
  (FLT.Mazur.HilbertChart.AffineRestriction.snd f hL d V c k).left)
local notation "W" => A.left.basicOpen s.val

/-- The actual full restricted Hilbert relation has exactly the localized original invariants. -/
def principalFullInvariantEquiv : Localization.Away s ≃+*
    compatibleFunctions (SchemeRelationRestriction.fst (p).left (q).left (W).ι)
      (SchemeRelationRestriction.snd (p).left (q).left (W).ι) :=
  @SchemeRelationPrincipalLocalization.fullEquiv
    (Rel).left A.left (p).left (q).left s inferInstance inferInstance
    (relation_compactSpace f hL d V c k) (relation_quasiSeparatedSpace f hL d V c k)

/-- The full Hilbert comparison is the unchanged structure-sheaf restriction on coefficients. -/
theorem principalFullInvariantEquiv_coefficients (a : compatibleFunctions (p).left (q).left) :
    (principalFullInvariantEquiv f hL d V c k s
      (algebraMap _ (Localization.Away s) a)).val = (W).ι.appTop a.val :=
  @SchemeRelationPrincipalLocalization.fullEquiv_algebraMap
    (Rel).left A.left (p).left (q).left s inferInstance inferInstance
    (relation_compactSpace f hL d V c k) (relation_quasiSeparatedSpace f hL d V c k) a

/-- The full flat tensor equalizer is realized in the actual original Hilbert open sections. -/
def principalTensorInvariantEquiv : Localization.Away s ≃+*
    relationOpenFunctions (p).left (q).left W (compatibleFunctions_basicOpen (p).left (q).left s) :=
  @SchemeRelationPrincipalLocalization.scalarSectionEquiv
    (Rel).left A.left (p).left (q).left s inferInstance inferInstance
    (relation_compactSpace f hL d V c k) (relation_quasiSeparatedSpace f hL d V c k)

/-- The original invariant affine candidates are compatible by an actual open immersion. -/
def principalInvariantCandidateMap :
    target (SchemeRelationRestriction.fst (p).left (q).left (W).ι)
      (SchemeRelationRestriction.snd (p).left (q).left (W).ι) ⟶ target (p).left (q).left :=
  @SchemeRelationPrincipalLocalization.candidateOpenMap
    (Rel).left A.left (p).left (q).left s inferInstance inferInstance
    (relation_compactSpace f hL d V c k) (relation_quasiSeparatedSpace f hL d V c k)

instance principalInvariantCandidateMap_isOpenImmersion :
    IsOpenImmersion (principalInvariantCandidateMap f hL d V c k s) :=
  @SchemeRelationPrincipalLocalization.candidateOpenMap_isOpenImmersion
    (Rel).left A.left (p).left (q).left s inferInstance inferInstance
    (relation_compactSpace f hL d V c k) (relation_quasiSeparatedSpace f hL d V c k)

/-- The complete source-projection square commutes, including every original coefficient map. -/
@[reassoc]
theorem principalInvariantCandidateMap_projection :
    projection (SchemeRelationRestriction.fst (p).left (q).left (W).ι)
      (SchemeRelationRestriction.snd (p).left (q).left (W).ι) ≫
      principalInvariantCandidateMap f hL d V c k s =
      (W).ι ≫ projection (p).left (q).left :=
  @SchemeRelationPrincipalLocalization.candidateOpenMap_projection
    (Rel).left A.left (p).left (q).left s inferInstance inferInstance
    (relation_compactSpace f hL d V c k) (relation_quasiSeparatedSpace f hL d V c k)

/-- The principal candidate keeps the unchanged original base map. -/
def principalRelativeInvariantModel : Over (Spec (.of R)) :=
  Over.mk (principalInvariantCandidateMap f hL d V c k s ≫
    (invariantAffineModel f hL d V c k).hom)

/-- Its open immersion is a morphism over the original base. -/
def principalRelativeCandidateMap : principalRelativeInvariantModel f hL d V c k s ⟶
    invariantAffineModel f hL d V c k :=
  Over.homMk (principalInvariantCandidateMap f hL d V c k s) rfl

/-- The actual restricted source keeps the original structural morphism. -/
def principalInvariantSource : Over (Spec (.of R)) := Over.mk ((W).ι ≫ A.hom)

/-- The full restricted relation's projection retains the original relative structure. -/
def principalRelativeProjection : principalInvariantSource f hL d V c k s ⟶
    principalRelativeInvariantModel f hL d V c k s :=
  Over.homMk (projection (SchemeRelationRestriction.fst (p).left (q).left (W).ι)
      (SchemeRelationRestriction.snd (p).left (q).left (W).ι)) (by
    change projection (SchemeRelationRestriction.fst (p).left (q).left (W).ι)
      (SchemeRelationRestriction.snd (p).left (q).left (W).ι) ≫
      principalInvariantCandidateMap f hL d V c k s ≫
      (invariantAffineModel f hL d V c k).hom = (W).ι ≫ A.hom
    rw [← Category.assoc, principalInvariantCandidateMap_projection, Category.assoc]
    exact congrArg (fun t ↦ (W).ι ≫ t) (invariantAffineProjection f hL d V c k).w)

/-- Full invariant local sections have genuine original invariant numerators. -/
theorem principal_invariant_numerator
    (z : relationOpenFunctions (p).left (q).left W
      (compatibleFunctions_basicOpen (p).left (q).left s)) :
    ∃ (a : compatibleFunctions (p).left (q).left) (n : ℕ),
      z.val * algebraMap Γ(A.left, ⊤) Γ(A.left, W) (s.val ^ n) =
        algebraMap Γ(A.left, ⊤) Γ(A.left, W) a.val :=
  @SchemeRelationPrincipalLocalization.exists_invariant_numerator
    (Rel).left A.left (p).left (q).left s inferInstance inferInstance
    (relation_compactSpace f hL d V c k) (relation_quasiSeparatedSpace f hL d V c k) z

end FLT.Mazur.HilbertChart.AffineRestriction
