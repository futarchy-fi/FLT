/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelPrincipalCover
public import FLT.Mazur.AffineGenericFlatOpen

/-!
# Actual flat projections on integral strata of the finite model patches

For every prime ideal of a selected principal target, pull back the entire
original source to the associated reduced integral closed stratum. Generic
flatness then constructs a dense principal open of this stratum on which the
actual source projection is surjective, flat and locally finitely presented.
This does not discard the need to recover nonreduced structure, cover residual
strata, or identify the full original Picard relation with the candidate kernel.
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
variable (r : Γ((finiteKernelModel f hL d V c k).left, ⊤))
local notation "Y" => Scheme.Opens.toScheme (Scheme.basicOpen (Over.left Q) r)
local notation "g" => finiteModelPrincipalProjection f hL d V c k r
variable (P : Ideal Γ(((finiteKernelModel f hL d V c k).left.basicOpen r).toScheme, ⊤))
  [P.IsPrime]

/-- The actual reduced integral closed stratum in the selected affine target. -/
def finiteModelStratumMap : Spec (.of (Γ(Y, ⊤) ⧸ P)) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P)) ≫ (Y).isoSpec.inv

local notation "i" => finiteModelStratumMap f hL d V c k r P

/-- The complete original-source pullback to this stratum. -/
def finiteModelStratumProjection : pullback g i ⟶ Spec (.of (Γ(Y, ⊤) ⧸ P)) :=
  pullback.snd g i

local notation "q" => finiteModelStratumProjection f hL d V c k r P

instance finiteModelStratumSource_isAffine : IsAffine (pullback g i) := by
  infer_instance

instance finiteModelStratumProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation q :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd g i))

omit [P.IsPrime] in
/-- Surjectivity holds on every prime stratum of each selected image patch. -/
theorem finiteModelStratumProjection_surjective
    (hr : r ∈ finiteModelPrincipalCoefficients f hL d V c k) : Surjective q := by
  let _ := finiteModelPrincipalProjection_surjective f hL d V c k r hr
  exact inferInstanceAs (Surjective (pullback.snd g i))

/-- A nonzero coefficient in the stratum ring, constructed from the original-source algebra. -/
def finiteModelStratumFlatCoefficient : Γ(Y, ⊤) ⧸ P :=
  AffineGenericFlatOpen.coefficient q

theorem finiteModelStratumFlatCoefficient_ne_zero :
    finiteModelStratumFlatCoefficient f hL d V c k r P ≠ 0 :=
  AffineGenericFlatOpen.coefficient_ne_zero q

/-- The dense principal open in the actual reduced integral target stratum. -/
def finiteModelStratumFlatTargetMap :
    Spec (.of (Localization.Away (finiteModelStratumFlatCoefficient f hL d V c k r P))) ⟶
      Spec (.of (Γ(Y, ⊤) ⧸ P)) := AffineGenericFlatOpen.targetMap q

local notation "j" => finiteModelStratumFlatTargetMap f hL d V c k r P

instance finiteModelStratumFlatTarget_isOpenImmersion : IsOpenImmersion j :=
  AffineGenericFlatOpen.targetMap_isOpenImmersion q

instance finiteModelStratumFlatTarget_isDominant : IsDominant j :=
  AffineGenericFlatOpen.targetMap_isDominant q

/-- The actual iterated source pullback has a proved flat projection. -/
instance finiteModelStratumFlatProjection_flat : Flat (pullback.fst j q) :=
  AffineGenericFlatOpen.projection_flat q

instance finiteModelStratumFlatProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (pullback.fst j q) := inferInstance

instance finiteModelStratumFlatProjection_quasiCompact :
    QuasiCompact (pullback.fst j q) := by infer_instance

/-- These constructed stratum projections really are fppf; no effectivity is assumed. -/
theorem finiteModelStratumFlatProjection_surjective
    (hr : r ∈ finiteModelPrincipalCoefficients f hL d V c k) :
    Surjective (pullback.fst j q) := by
  let _ := finiteModelStratumProjection_surjective f hL d V c k r P hr
  infer_instance

end FLT.Mazur.HilbertChart.AffineRestriction
