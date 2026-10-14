/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteModelFlatStratum

/-!
# Original-base maps for the complete flat stratum source

Compose the principal-open, integral-stratum, and generic-flatness squares.
The complete iterated source is the actual pullback of the original finite
model projection, with its original structural map retained.
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

omit [P.IsPrime] in
/-- The actual stratum map is a closed immersion, including its scheme structure. -/
instance finiteModelStratumMap_isClosedImmersion : IsClosedImmersion i := by
  unfold finiteModelStratumMap
  let _ : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

/-- The composed flat-stratum inclusion lands in the unchanged finite coefficient model. -/
def finiteModelStratumFlatToModel :
    Spec (.of (Localization.Away (finiteModelStratumFlatCoefficient f hL d V c k r P))) ⟶
      (Q).left := j ≫ i ≫ (U).ι

instance finiteModelStratumFlatToModel_mono :
    Mono (finiteModelStratumFlatToModel f hL d V c k r P) := by
  unfold finiteModelStratumFlatToModel
  infer_instance

/-- The entire iterated source retains its original structural morphism. -/
def finiteModelStratumFlatSource : Over (Spec (.of R)) :=
  Over.mk (pullback.snd j q ≫ pullback.fst g i ≫ ((v).left ⁻¹ᵁ U).ι ≫ A.hom)

/-- The actual source comparison forgets only the extra base-change coordinates. -/
def finiteModelStratumFlatSourceMap : finiteModelStratumFlatSource f hL d V c k r P ⟶ A :=
  Over.homMk (pullback.snd j q ≫ pullback.fst g i ≫ ((v).left ⁻¹ᵁ U).ι)

/-- All three constructed squares paste to the original finite-model projection. -/
theorem finiteModelStratumFlatSource_isPullback :
    IsPullback (finiteModelStratumFlatSourceMap f hL d V c k r P).left
      (pullback.fst j q) (v).left (finiteModelStratumFlatToModel f hL d V c k r P) := by
  have h₁ := (IsPullback.of_hasPullback j q).flip
  have h₂ := IsPullback.of_hasPullback g i
  have h₃ := (isPullback_morphismRestrict (v).left U).flip
  exact (h₁.paste_horiz (h₂.paste_horiz h₃))

/-- No branch is selected from the original-source pullback. -/
instance finiteModelStratumFlatSourceMap_mono :
    Mono (finiteModelStratumFlatSourceMap f hL d V c k r P).left :=
  (finiteModelStratumFlatSource_isPullback f hL d V c k r P).mono_fst_of_mono

end FLT.Mazur.HilbertChart.AffineRestriction
