/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFlatStratumSource
public import FLT.Mazur.AffineHilbertMonicRelationGeometry

/-!
# The full Picard relation on the actual flat stratum source

The complete W256 source carries the unchanged original Picard section and
its full relation. Both endpoint squares are actual pullbacks, hence the
endpoints are étale and surjective. The relation maps monomorphically to the
kernel of the proved fppf projection; equality with that kernel is still open.
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

/-- The entire new relation is exactly the full two-endpoint restriction of the old relation. -/
def finiteModelStratumFlatFullRelationIso : (relation f hL d V c (u ≫ k)).left ≅
    SchemeRelationRestriction.doubleDomain (fst f hL d V c k).left
      (snd f hL d V c k).left (u).left :=
  nestedSchemeDoubleIso f hL d V c k u

/-- The comparison retains the original first endpoint and every arrow above it. -/
theorem finiteModelStratumFlatRelation_fst_isPullback :
    IsPullback (α).left (p').left (fst f hL d V c k).left (u).left :=
  monicModelRelation_fst_isPullback f hL d V c k u t (pullback.fst j q) H

/-- The second original endpoint also survives as an entire base change. -/
theorem finiteModelStratumFlatRelation_snd_isPullback :
    IsPullback (α).left (q').left (snd f hL d V c k).left (u).left :=
  monicModelRelation_snd_isPullback f hL d V c k u t (pullback.fst j q) H

/-- The full original first endpoint remains étale on the constructed source. -/
instance finiteModelStratumFlatRelation_fst_etale : Etale (p').left :=
  monicModelRelation_fst_etale f hL d V c k u t (pullback.fst j q) H

/-- The independent second endpoint is likewise étale. -/
instance finiteModelStratumFlatRelation_snd_etale : Etale (q').left :=
  monicModelRelation_snd_etale f hL d V c k u t (pullback.fst j q) H

/-- Every source point remains the endpoint of an original identity arrow. -/
instance finiteModelStratumFlatRelation_fst_surjective : Surjective (p').left :=
  monicModelRelation_fst_surjective f hL d V c k u t (pullback.fst j q) H

/-- The same identity arrows prove surjectivity of the second endpoint. -/
instance finiteModelStratumFlatRelation_snd_surjective : Surjective (q').left :=
  monicModelRelation_snd_surjective f hL d V c k u t (pullback.fst j q) H

/-- The actual fppf projection coequalizes the full original Picard relation. -/
@[reassoc]
theorem finiteModelStratumFlatRelation_condition :
    (p').left ≫ pullback.fst j q = (q').left ≫ pullback.fst j q :=
  monicModelRelation_condition f hL d V c k u t (pullback.fst j q) H

/-- The full original relation, rather than an independent replacement, maps to the kernel. -/
def finiteModelStratumFlatRelationKernelMap : (relation f hL d V c (u ≫ k)).left ⟶
    pullback (pullback.fst j q) (pullback.fst j q) :=
  monicModelRelationKernelMap f hL d V c k u t (pullback.fst j q) H

/-- Every original arrow is retained. Surjectivity of this map has not been assumed. -/
instance finiteModelStratumFlatRelationKernelMap_mono :
    Mono (finiteModelStratumFlatRelationKernelMap f hL d V c k r P) :=
  inferInstanceAs (Mono (monicModelRelationKernelMap f hL d V c k u t (pullback.fst j q) H))

end FLT.Mazur.HilbertChart.AffineRestriction
