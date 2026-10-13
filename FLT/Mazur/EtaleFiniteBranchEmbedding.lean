/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleFiniteBranchScheme

/-!
# The finite branch is an open-and-closed part of the full base change

The idempotent localization is surjective on coordinate rings, so its
already constructed open immersion is also closed. Composing with the
actual tensor-product pullback isomorphism retains both projections.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
universe u
namespace FLT.Mazur.EtaleFiniteBranchScheme
set_option backward.isDefEq.respectTransparency false
variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] (e : C ⊗[A] B)

/-- Idempotent branches are closed as well as open in the full tensor scheme. -/
theorem inclusion_isClosedImmersion (he : IsIdempotentElem e) :
    IsClosedImmersion (inclusion e) :=
  IsClosedImmersion.spec_of_surjective _
    (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he)

/-- The branch embeds in the categorical full base change of the original affine map. -/
def toPullback : branch e ⟶
    pullback (Spec.map (CommRingCat.ofHom (algebraMap A C)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
  inclusion e ≫ tensor_isPullback.isoPullback.hom

instance toPullback_isOpenImmersion : IsOpenImmersion (toPullback e) :=
  inferInstanceAs (IsOpenImmersion (inclusion e ≫ tensor_isPullback.isoPullback.hom))

/-- The constructed branch is a closed component of the full coefficient pullback. -/
theorem toPullback_isClosedImmersion (he : IsIdempotentElem e) :
    IsClosedImmersion (toPullback e) := by
  let _ := inclusion_isClosedImmersion e he
  exact inferInstanceAs (IsClosedImmersion (inclusion e ≫ tensor_isPullback.isoPullback.hom))

/-- The first projection is the constructed finite coefficient map. -/
@[reassoc]
theorem toPullback_fst : toPullback e ≫ pullback.fst _ _ = coefficient e := by
  rw [toPullback, Category.assoc, IsPullback.isoPullback_hom_fst, inclusion_coefficient]

/-- The other projection is the etale map to the original affine source. -/
@[reassoc]
theorem toPullback_snd : toPullback e ≫ pullback.snd _ _ = original e := by
  rw [toPullback, Category.assoc, IsPullback.isoPullback_hom_snd]
  rfl

end FLT.Mazur.EtaleFiniteBranchScheme
