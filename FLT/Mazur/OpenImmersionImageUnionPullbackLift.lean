/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionImageUnionPullback

/-!
# Extending literal routes across a full union pullback

Factorizations on every literal double overlap force a factorization on
the whole ambient intersection. Equations after a further comparison
also extend to that entire domain.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur

universe u v w

variable {X Y : Scheme.{u}} {ι : Type v} {κ : Type w}
  {V : ι → Scheme.{u}} {W : κ → Scheme.{u}}
  (f : ∀ i, V i ⟶ X) (g : ∀ j, W j ⟶ X)
  [∀ i, IsOpenImmersion (f i)] [∀ j, IsOpenImmersion (g j)]
  (a : pullback (openImageUnion f).ι (openImageUnion g).ι ⟶ Y) (U : Y.Opens)
  (r : ∀ i j, pullback (f i) (g j) ⟶ U.toScheme)
  (hr : ∀ i j, r i j ≫ U.ι = openImageUnionPullbackMap f g i j ≫ a)

include hr in
/-- Literal factorizations give the required image inclusion on the entire pullback. -/
theorem openImageUnionPullback_image_le : Set.range a ⊆ (U : Set Y) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨⟨i, j⟩, w, rfl⟩ := (openImageUnionPullbackCover f g).exists_eq z
  change (openImageUnionPullbackMap f g i j ≫ a) w ∈ U
  rw [← hr]
  exact (r i j w).2

/-- Construct the map on the full ambient pullback using its literal double-overlap cover. -/
def openImageUnionPullbackLift :
    pullback (openImageUnion f).ι (openImageUnion g).ι ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι a (by
    rw [← Scheme.Hom.coe_opensRange U.ι, Scheme.Opens.opensRange_ι]
    exact openImageUnionPullback_image_le f g a U r hr)

/-- The constructed full-domain map retains the ambient route. -/
@[reassoc] theorem openImageUnionPullbackLift_fac :
    openImageUnionPullbackLift f g a U r hr ≫ U.ι = a :=
  IsOpenImmersion.lift_fac _ _ _

/-- The full-domain lift restricts to each prescribed literal route. -/
@[reassoc] theorem openImageUnionPullbackLift_component (i : ι) (j : κ) :
    openImageUnionPullbackMap f g i j ≫ openImageUnionPullbackLift f g a U r hr = r i j := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, openImageUnionPullbackLift_fac, hr]

/-- An open ambient route gives an open immersion on the entire pullback. -/
instance openImageUnionPullbackLift_isOpenImmersion [IsOpenImmersion a] :
    IsOpenImmersion (openImageUnionPullbackLift f g a U r hr) := by
  dsimp only [openImageUnionPullbackLift]
  infer_instance

/-- Comparison equations on all literal patches hold on the full ambient pullback. -/
theorem openImageUnionPullbackLift_comparison {Z : Scheme.{u}} (c : U.toScheme ⟶ Z)
    (b : pullback (openImageUnion f).ι (openImageUnion g).ι ⟶ Z)
    (he : ∀ i j, r i j ≫ c = openImageUnionPullbackMap f g i j ≫ b) :
    openImageUnionPullbackLift f g a U r hr ≫ c = b := by
  apply openImageUnionPullback_hom_ext f g
  intro i j
  rw [← Category.assoc, openImageUnionPullbackLift_component]
  exact he i j

end FLT.Mazur
