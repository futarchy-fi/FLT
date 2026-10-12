/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEnvelopeKernelPair
public import FLT.Mazur.RelativeRelationFpqcInvariantQuotient

/-!
# Effective original invariant quotient for a full Hilbert envelope

When the translation base is faithfully flat and the full relation fills its
original affine envelope, its original invariant locally ringed quotient is
the constructed fixed-algebra spectrum, including the entire structure sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsIso (toEnvelope f hL d V c k).left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k

/-- The constructed affine invariant spectrum over the ORIGINAL base. -/
def fullEnvelopeTarget : Over (Spec (.of R)) := Over.mk (fullEnvelopeBase f hL d V c k)

/-- The original source projection, retaining its original relative structure. -/
def fullEnvelopeRelativeProjection : A ⟶ fullEnvelopeTarget f hL d V c k :=
  Over.homMk (fullEnvelopeProjection f hL d V c k) (fullEnvelopeProjection_base f hL d V c k)

/-- The original relative relation remains the complete kernel pair. -/
theorem fullEnvelope_relative_kernelPair [Flat V.hom] :
    IsPullback p q (fullEnvelopeRelativeProjection f hL d V c k)
      (fullEnvelopeRelativeProjection f hL d V c k) :=
  IsPullback.of_map_of_faithful (Over.forget _) (fullEnvelope_kernelPair f hL d V c k)

instance fullEnvelopeTarget_affine : IsAffine (fullEnvelopeTarget f hL d V c k).left := by
  change IsAffine (fullEnvelopeScheme f hL d V c k)
  unfold fullEnvelopeScheme AffineAlgebraDescent.descendedScheme
  infer_instance

instance fullEnvelopeRelativeProjection_quasiCompact :
    QuasiCompact (fullEnvelopeRelativeProjection f hL d V c k).left := by
  infer_instance

instance fullEnvelopeRelativeProjection_flat [Flat V.hom] :
    Flat (fullEnvelopeRelativeProjection f hL d V c k).left :=
  MorphismProperty.of_isPullback (fullEnvelope_isPullback f hL d V c k).flip
    (inferInstanceAs (Flat V.hom))

instance fullEnvelopeRelativeProjection_surjective [Flat V.hom] [Surjective V.hom] :
    Surjective (fullEnvelopeRelativeProjection f hL d V c k).left :=
  MorphismProperty.of_isPullback (fullEnvelope_isPullback f hL d V c k).flip
    (inferInstanceAs (Surjective V.hom))

variable [Flat V.hom] [Surjective V.hom]

/-- The ORIGINAL invariant locally ringed quotient is the constructed affine scheme. -/
def fullEnvelopeInvariantQuotientIso : invariantLocallyRingedSpace e ≅
    (fullEnvelopeScheme f hL d V c k).toLocallyRingedSpace :=
  fpqcInvariantQuotientIso e (fullEnvelopeRelativeProjection f hL d V c k)
    (fullEnvelope_relative_kernelPair f hL d V c k)

/-- The quotient isomorphism retains the original source projection. -/
@[reassoc]
theorem fullEnvelopeInvariantQuotientIso_projection :
    invariantLocallyRingedProjection e ≫ (fullEnvelopeInvariantQuotientIso f hL d V c k).hom =
      (fullEnvelopeProjection f hL d V c k).toLRSHom :=
  fpqcInvariantQuotientIso_projection e (fullEnvelopeRelativeProjection f hL d V c k)
    (fullEnvelope_relative_kernelPair f hL d V c k)

/-- The comparison preserves the ORIGINAL R-base map. -/
theorem fullEnvelopeInvariantQuotientIso_base :
    (fullEnvelopeInvariantQuotientIso f hL d V c k).hom ≫
      (fullEnvelopeBase f hL d V c k).toLRSHom = invariantLocallyRingedBaseMap e :=
  fpqcInvariantQuotientIso_baseMap e (fullEnvelopeRelativeProjection f hL d V c k)
    (fullEnvelope_relative_kernelPair f hL d V c k)

/-- The constructed projection is effective for arbitrary scheme targets. -/
def fullEnvelopeCoforkIsColimit : IsColimit (Cofork.ofπ
    (fullEnvelopeProjection f hL d V c k) (fullEnvelopeProjection_equalizes f hL d V c k)) := by
  let _ : Flat (fullEnvelopeProjection f hL d V c k) :=
    fullEnvelopeRelativeProjection_flat f hL d V c k
  let _ : Surjective (fullEnvelopeProjection f hL d V c k) :=
    fullEnvelopeRelativeProjection_surjective f hL d V c k
  let _ : QuasiCompact (fullEnvelopeProjection f hL d V c k) :=
    fullEnvelopeRelativeProjection_quasiCompact f hL d V c k
  exact isColimitCoforkOfEffectiveEpi (fullEnvelopeProjection f hL d V c k) _
    (fullEnvelope_kernelPair f hL d V c k).isLimit

end FLT.Mazur.HilbertChart.AffineRestriction
