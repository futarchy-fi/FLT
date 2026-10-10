/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Products of finite families of sections

The product over a scheme of two finite coproducts of that scheme is the
coproduct indexed by pairs. The comparison is the actual pair of inclusions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace FLT.Mazur.SchemeSectionFamilyProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

variable (S : Scheme.{u}) (I J : Type u) [Finite I] [Finite J]

/-- The finite section families form the expected Cartesian square. -/
theorem isPullback :
    IsPullback
      (Sigma.desc fun p : I × J => Sigma.ι (fun _ : I => S) p.1)
      (Sigma.desc fun p : I × J => Sigma.ι (fun _ : J => S) p.2)
      (Sigma.desc fun _ : I => 𝟙 S) (Sigma.desc fun _ : J => 𝟙 S) := by
  convert! IsUniversalColimit.isPullback_prod_of_isColimit
    (a := Cofan.mk _ (Sigma.ι fun _ : I => S))
    (b := Cofan.mk _ (Sigma.ι fun _ : J => S))
    (FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct _))
    (FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct _))
    (fun _ : I => 𝟙 S) (fun _ : J => 𝟙 S)
    (Sigma.desc fun _ : I => 𝟙 S) (Sigma.desc fun _ : J => 𝟙 S)
    (fun _ _ => IsPullback.of_id_fst (f := 𝟙 S))
    (Cofan.mk _ (Sigma.ι fun _ : I × J => S)) (coproductIsCoproduct _) using 1

/-- The comparison isomorphism from paired summands to the actual fiber product. -/
def iso : (∐ fun _ : I × J => S) ≅
    pullback (Sigma.desc fun _ : I => 𝟙 S) (Sigma.desc fun _ : J => 𝟙 S) :=
  (isPullback S I J).isoPullback

/-- First projection of the actual comparison. -/
@[reassoc] theorem iso_hom_fst :
    (iso S I J).hom ≫ pullback.fst _ _ =
      Sigma.desc fun p : I × J => Sigma.ι (fun _ : I => S) p.1 :=
  (isPullback S I J).isoPullback_hom_fst

/-- Second projection of the actual comparison. -/
@[reassoc] theorem iso_hom_snd :
    (iso S I J).hom ≫ pullback.snd _ _ =
      Sigma.desc fun p : I × J => Sigma.ι (fun _ : J => S) p.2 :=
  (isPullback S I J).isoPullback_hom_snd

end FLT.Mazur.SchemeSectionFamilyProduct
