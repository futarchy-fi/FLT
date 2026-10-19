/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluDescendedMorphism

/-!
# Point values of the actual descended Vélu morphism

The coefficient square gives the original geometric coordinate map on every
point. Faithfully flat cancellation then identifies its base-field values with
any point map having the original scalar-extension compatibility.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [CharZero K] [CharZero L] [Algebra.IsAlgebraic K L] [IsAlgClosed L] [DecidableEq L]
  (E : WeierstrassCurve K) [E.IsElliptic]
  (G : AddSubgroup (E.map (algebraMap K L)).toAffine.Point) [Fintype G]
  (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)
  (V : WeierstrassCurve K)
  (hV : V.map (algebraMap K L) = curve (E.map (algebraMap K L)) G)
  (hG : ∀ (g : L ≃ₐ[K] L) P, P ∈ G →
    Affine.Point.map (W' := E.toAffine) g.toAlgHom P ∈ G)
  (h : ∀ P, P ∉ G → (V.map (algebraMap K L)).toAffine.Nonsingular
    (xMap (E.map (algebraMap K L)) G P) (yMap (E.map (algebraMap K L)) G P))

local notation "EL" => E.map (algebraMap K L)
local notation "VL" => V.map (algebraMap K L)

/-- The descended map evaluates to the original coordinate sums at every geometric point. -/
@[reassoc] theorem veluDescendedMorphism_pointMap (P : (EL).toAffine.Point) :
    (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) ≫
        veluDescendedMorphism E G hodd V hV hG =
      affineSmoothPoint V (pointMap EL G VL h P) ≫ (integralSmoothOpen V).ι := by
  rw [← affineSmoothPoint_coefficient E P, Category.assoc, veluDescendedMorphism_fac]
  exact veluGlobalToBaseTarget_pointMap E G hodd V hV h P

/-- Every original base-field point agrees with its descended coordinate value. -/
@[reassoc] theorem veluDescendedMorphism_basePoint [DecidableEq K]
    (P : (E.map (algebraMap K K)).toAffine.Point)
    (Q : (V.map (algebraMap K K)).toAffine.Point)
    (hQ : Affine.Point.baseChange (W' := V.toAffine) K L Q =
      pointMap EL G VL h (Affine.Point.baseChange (W' := E.toAffine) K L P)) :
    (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) ≫
        veluDescendedMorphism E G hodd V hV hG =
      affineSmoothPoint V Q ≫ (integralSmoothOpen V).ι := by
  have H := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap K L))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  let _ := H.1
  let _ := H.2
  let _ := Flat.epi_of_flat_of_surjective (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  apply (cancel_epi (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mp
  rw [← Category.assoc]
  change (Spec.map (CommRingCat.ofHom (Algebra.ofId K L).toRingHom) ≫ _) ≫ _ =
    Spec.map (CommRingCat.ofHom (Algebra.ofId K L).toRingHom) ≫ _
  rw [affineSmoothPoint_natural E (Algebra.ofId K L),
    affineSmoothPoint_natural V (Algebra.ofId K L),
    veluDescendedMorphism_pointMap E G hodd V hV hG h]
  exact congrArg (fun R ↦ affineSmoothPoint V R ≫ (integralSmoothOpen V).ι) hQ.symm

end WeierstrassCurve.Velu
