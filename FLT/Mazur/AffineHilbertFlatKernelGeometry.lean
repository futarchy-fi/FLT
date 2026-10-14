/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertBoundedRelation
public import FLT.Mazur.AffineHilbertFlatStratumRelation
public import FLT.Mazur.AffineHilbertMonicKernelGeometry

/-!
# Finite geometry of the complete flat-stratum kernel comparison

The original full Picard relation maps by a quasi-compact, unramified,
locally finitely presented monomorphism into an affine Noetherian kernel.
Its image is constructible. Equality with that entire kernel remains open.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
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
variable (P : Ideal Γ(((finiteKernelModel f hL d V c k).left.basicOpen r).toScheme, ⊤))
  [P.IsPrime]
local notation "i" => finiteModelStratumMap f hL d V c k r P
local notation "q" => finiteModelStratumProjection f hL d V c k r P
local notation "j" => finiteModelStratumFlatTargetMap f hL d V c k r P

local notation "u" => finiteModelStratumFlatSourceMap f hL d V c k r P
local notation "t" => finiteModelStratumFlatToModel f hL d V c k r P
local notation "p'" => fst f hL d V c (u ≫ k)
local notation "q'" => snd f hL d V c (u ≫ k)
local notation "α" => nestedToFullRelation f hL d V c k u
local notation "H" => finiteModelStratumFlatSource_isPullback f hL d V c k r P

local notation "m" => finiteModelStratumFlatRelationKernelMap f hL d V c k r P
local notation "w" => pullback.fst j q

/-- Noetherianity of the actual flat target follows geometrically along its two inclusions. -/
instance finiteModelStratumFlatTarget_isLocallyNoetherian :
    IsLocallyNoetherian
      (Spec (.of (Localization.Away (finiteModelStratumFlatCoefficient f hL d V c k r P)))) := by
  let _ : IsLocallyNoetherian (U).toScheme := inferInstance
  let _ := LocallyOfFiniteType.isLocallyNoetherian i
  exact LocallyOfFiniteType.isLocallyNoetherian j

/-- The complete iterated source is affine, not merely covered by selected affine branches. -/
instance finiteModelStratumFlatSource_isAffine :
    IsAffine (finiteModelStratumFlatSource f hL d V c k r P).left := by
  change IsAffine (pullback j q)
  infer_instance

/-- The actual candidate kernel is affine. -/
instance finiteModelStratumFlatKernel_isAffine : IsAffine (pullback w w) := by
  infer_instance

/-- The actual candidate kernel is locally Noetherian, before any effectivity assertion. -/
instance finiteModelStratumFlatKernel_isLocallyNoetherian :
    IsLocallyNoetherian (pullback w w) :=
  monicModelKernel_isLocallyNoetherian f hL d V c k u t w H

/-- Affineness makes the full locally Noetherian kernel Noetherian. -/
instance finiteModelStratumFlatKernel_isNoetherian : IsNoetherian (pullback w w) := ⟨⟩

/-- The entire source, including all arrows used for comparison, is locally Noetherian. -/
instance finiteModelStratumFlatSource_isLocallyNoetherian :
    IsLocallyNoetherian (finiteModelStratumFlatSource f hL d V c k r P).left :=
  monicModelSource_isLocallyNoetherian f hL d V c k u t w H

/-- Quasi-compactness retains the complete original endpoint fiber over the flat source. -/
instance finiteModelStratumFlatRelation_fst_quasiCompact : QuasiCompact (p').left :=
  monicModelRelation_fst_quasiCompact f hL d V c k u t w H

/-- The entire retained original relation is Noetherian. -/
instance finiteModelStratumFlatRelation_isNoetherian :
    IsNoetherian (relation f hL d V c (u ≫ k)).left := by
  let _ := LocallyOfFiniteType.isLocallyNoetherian (p').left
  let _ := QuasiCompact.compactSpace_of_compactSpace (p').left
  exact ⟨⟩

/-- The whole kernel comparison is quasi-compact. -/
instance finiteModelStratumFlatRelationKernelMap_quasiCompact : QuasiCompact m := by
  infer_instance

/-- Finite presentation concerns the comparison itself, not only its endpoint projections. -/
instance finiteModelStratumFlatRelationKernelMap_locallyOfFinitePresentation :
    LocallyOfFinitePresentation m :=
  inferInstanceAs (LocallyOfFinitePresentation
    (monicModelRelationKernelMap f hL d V c k u t w H))

/-- The complete comparison is unramified. -/
instance finiteModelStratumFlatRelationKernelMap_formallyUnramified : FormallyUnramified m :=
  inferInstanceAs (FormallyUnramified (monicModelRelationKernelMap f hL d V c k u t w H))

/-- Its exact image in the actual kernel is constructible. -/
theorem finiteModelStratumFlatRelationKernelMap_range_constructible :
    IsConstructible (Set.range m) := by
  simpa only [Set.image_univ] using (m).isConstructible_image IsConstructible.univ

end FLT.Mazur.HilbertChart.AffineRestriction
