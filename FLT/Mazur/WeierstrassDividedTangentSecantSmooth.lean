/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedReciprocalChordTangentSmooth
public import FLT.Mazur.WeierstrassDividedTangentSecantScheme
public import FLT.Mazur.WeierstrassDividedSuppliedSmoothSecantDomain

/-!
# Tangent/secant comparison on the actual smooth image domains

Transport the whole formula comparison to the unchanged input scheme and
then to the full finite smooth model, on arbitrary nonreduced refinements.
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
local notation "T" => suppliedSmoothTangentDomain d a c
local notation "C" => suppliedSmoothSecantDomain d a c
local notation "vc" => suppliedSmoothSecantSmoothOpen d a c
local notation "vt" => suppliedSmoothTangentSmoothOpen d a c
local notation "ic" => suppliedSmoothSecantSmoothInclusion d a c

/-- Recover the actual localized source from the smooth secant image open. -/
def suppliedSecantDomainSource : (C).toScheme ⟶
    Spec (.of (DividedSecantRing W (π ^ k) d.b3 d.b4 d.b6 a c)) :=
  (ic).isoOpensRange.inv ≫ (vc).ι

/-- The recovered secant source retains the unchanged input morphism. -/
@[reassoc] theorem suppliedSecantDomainSource_input :
    suppliedSecantDomainSource d a c ≫ suppliedSmoothSecantInclusion d a c = (C).ι := by
  exact Scheme.Hom.isoOpensRange_inv_comp ic

/-- Whole smooth outputs agree on every common scheme over the unchanged inputs. -/
theorem suppliedTangentSecant_original {X : Scheme.{u}}
    (f : X ⟶ (T).toScheme) (g : X ⟶ (C).toScheme) (h : f ≫ (T).ι = g ≫ (C).ι) :
    f ≫ suppliedSmoothTangentOriginalSmooth d a c =
      g ≫ suppliedSmoothSecantOriginalSmooth d a c := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  let ft := f ≫ suppliedTangentDomainSource d a c
  let gc := g ≫ suppliedSecantDomainSource d a c
  have hb : ft ≫ suppliedSmoothTangentInclusion d a c =
      gc ≫ suppliedSmoothSecantInclusion d a c := by
    simp only [ft, gc, Category.assoc, suppliedTangentDomainSource_input,
      suppliedSecantDomainSource_input, h]
  have he := dividedTangentSecant_scheme W (π ^ k) d.b3 d.b4 d.b6 a c
    d.factor3 d.factor4 d.factor6 ft gc hb
  simpa only [ft, gc, suppliedTangentDomainSource, suppliedSecantDomainSource,
    suppliedSmoothTangentOriginalSmooth, suppliedSmoothSecantOriginalSmooth,
    Category.assoc, morphismRestrict_ι, suppliedSmoothTangentSmoothOpen,
    suppliedSmoothSecantSmoothOpen] using he

variable [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)

/-- Tangent and secant outputs coincide in the same full finite smooth model. -/
theorem suppliedTangentSecant_resolved {X : Scheme.{u}}
    (f : X ⟶ (T).toScheme) (g : X ⟶ (C).toScheme) (h : f ≫ (T).ι = g ≫ (C).ι) :
    f ≫ suppliedSmoothTangentResolvedAddition d a c hπ data j hj =
      g ≫ suppliedSmoothSecantResolvedAddition d a c hπ data j hj := by
  simpa only [suppliedSmoothTangentResolvedAddition, suppliedSmoothSecantResolvedAddition,
    Category.assoc] using congrArg (fun z => z ≫ finiteOriginalToResolved hπ data j hj)
      (suppliedTangentSecant_original d a c f g h)

end FLT.Mazur.WeierstrassDividedDepth
