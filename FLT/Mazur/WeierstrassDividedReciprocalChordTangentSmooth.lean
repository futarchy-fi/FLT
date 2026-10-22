/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalChordTangentScheme
public import FLT.Mazur.WeierstrassDividedReciprocalChordSmoothDomain
public import FLT.Mazur.WeierstrassDividedSuppliedSmoothTangentDomain

/-!
# Reciprocal chord and tangent agreement on the actual smooth domains

Transport the comparison through both image-open isomorphisms. The whole
original smooth outputs, and hence their lifts into any common finite model,
agree on every scheme over the unchanged input source.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassIntegralChart
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {W : WeierstrassCurve R} {π : R} {k : ℕ} (d : Data W π k)
  (a c : WeierstrassDilatation.Coordinate W (π ^ k) d.b3 d.b4 d.b6 →ₐ[R] S)
local notation "C" => suppliedReciprocalChordDomain d a c
local notation "T" => suppliedSmoothTangentDomain d a c
local notation "vc" => suppliedReciprocalChordSmoothOpen d a c
local notation "vt" => suppliedSmoothTangentSmoothOpen d a c
local notation "ic" => suppliedReciprocalChordSmoothInclusion d a c
local notation "it" => suppliedSmoothTangentSmoothInclusion d a c

/-- Recover the actual localized source from the reciprocal chord image open. -/
def suppliedReciprocalChordDomainSource : (C).toScheme ⟶
    Spec (.of (DividedReciprocalChordOutputRing W (π ^ k) d.b3 d.b4 d.b6 a c)) :=
  (ic).isoOpensRange.inv ≫ (vc).ι

/-- Recover the actual localized source from the tangent image open. -/
def suppliedTangentDomainSource : (T).toScheme ⟶
    Spec (.of (DividedTangentRing W (π ^ k) d.b3 d.b4 d.b6 a c)) :=
  (it).isoOpensRange.inv ≫ (vt).ι

/-- The recovered reciprocal source lies over the unchanged input point. -/
@[reassoc] theorem suppliedReciprocalChordDomainSource_input :
    suppliedReciprocalChordDomainSource d a c ≫ suppliedReciprocalChordInclusion d a c =
      (C).ι := by
  exact Scheme.Hom.isoOpensRange_inv_comp ic

/-- The recovered tangent source lies over the unchanged input point. -/
@[reassoc] theorem suppliedTangentDomainSource_input :
    suppliedTangentDomainSource d a c ≫ suppliedSmoothTangentInclusion d a c = (T).ι := by
  exact Scheme.Hom.isoOpensRange_inv_comp it

/-- Image-open transport identifies the entire original smooth outputs on any overlap. -/
theorem suppliedReciprocalChordTangent_original {X : Scheme.{u}}
    (f : X ⟶ (C).toScheme) (g : X ⟶ (T).toScheme) (h : f ≫ (C).ι = g ≫ (T).ι) :
    f ≫ suppliedReciprocalChordOriginalSmooth d a c =
      g ≫ suppliedSmoothTangentOriginalSmooth d a c := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  let fc := f ≫ suppliedReciprocalChordDomainSource d a c
  let gt := g ≫ suppliedTangentDomainSource d a c
  have hb : fc ≫ suppliedReciprocalChordInclusion d a c =
      gt ≫ suppliedSmoothTangentInclusion d a c := by
    simp only [fc, gt, Category.assoc, suppliedReciprocalChordDomainSource_input,
      suppliedTangentDomainSource_input, h]
  let Q := DividedReciprocalChordRing W (π ^ k) d.b3 d.b4 d.b6 a c
  let B := DividedReciprocalChordOutputRing W (π ^ k) d.b3 d.b4 d.b6 a c
  have he : ((IsScalarTower.toAlgHom R Q B).comp (IsScalarTower.toAlgHom R S Q)).toRingHom =
      (algebraMap Q B).comp (algebraMap S Q) := by ext z; rfl
  have hc := dividedReciprocalChordTangent_scheme W (π ^ k) d.b3 d.b4 d.b6 a c
    d.factor3 d.factor4 d.factor6 fc gt (by
      rw [he, CommRingCat.ofHom_comp, Spec.map_comp]
      exact hb)
  simpa only [fc, gt, suppliedReciprocalChordDomainSource, suppliedTangentDomainSource,
    suppliedReciprocalChordOriginalSmooth, suppliedSmoothTangentOriginalSmooth,
    Category.assoc, morphismRestrict_ι, suppliedReciprocalChordSmoothOpen,
    suppliedSmoothTangentSmoothOpen] using hc

variable [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)

/-- The two constructed outputs coincide in the same full finite smooth model. -/
theorem suppliedReciprocalChordTangent_resolved {X : Scheme.{u}}
    (f : X ⟶ (C).toScheme) (g : X ⟶ (T).toScheme) (h : f ≫ (C).ι = g ≫ (T).ι) :
    f ≫ suppliedReciprocalChordResolvedAddition d a c hπ data j hj =
      g ≫ suppliedSmoothTangentResolvedAddition d a c hπ data j hj := by
  simpa only [suppliedReciprocalChordResolvedAddition, suppliedSmoothTangentResolvedAddition,
    Category.assoc] using congrArg (fun z => z ≫ finiteOriginalToResolved hπ data j hj)
      (suppliedReciprocalChordTangent_original d a c f g h)

end FLT.Mazur.WeierstrassDividedDepth
