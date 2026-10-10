/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisDirectSum

/-!
# Global linear maps from affine sum coordinates

Natural affine coordinates that preserve the original structure-sheaf action
produce actual global degree inclusions and finite-sum descent maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped DirectSum

universe u

namespace FLT.Mazur.AffineBasisSumMaps

variable {X : Scheme.{u}} (M : ℕ → X.Modules) (S : X.Modules)
  (e : AffineBasisModuleMorphism.basis S ≅ AffineBasisDirectSum.sum M)
  (he : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (s : Γ(S, U.1)),
    e.hom.hom.app (.op U) (r • s) = r •
      (show ⨁ n, Γ(M n, U.1) from e.hom.hom.app (.op U) s))

/-- The additive affine coordinates as an isomorphism of section groups. -/
def coordinates (U : X.affineOpens) :
    Γ(S, U.1) ≅ AddCommGrpCat.of (⨁ n, Γ(M n, U.1)) :=
  ((sheafToPresheaf _ _).mapIso e).app (.op U)

include he in
/-- Inverse coordinates preserve the original structure-sheaf scalar action. -/
lemma inv_smul (U : X.affineOpens) (r : Γ(X, U.1)) (s : ⨁ n, Γ(M n, U.1)) :
    e.inv.hom.app (.op U) (r • s) = r •
      (show Γ(S, U.1) from e.inv.hom.app (.op U) s) := by
  change (coordinates M S e U).inv (r • s) = r • (coordinates M S e U).inv s
  apply (ConcreteCategory.bijective_of_isIso (coordinates M S e U).hom).injective
  change (coordinates M S e U).hom ((coordinates M S e U).inv (r • s)) = _
  rw [Iso.inv_hom_id_apply]
  change r • s = e.hom.hom.app (.op U)
    (r • (show Γ(S, U.1) from e.inv.hom.app (.op U) s))
  rw [he]
  change r • s = r • ((coordinates M S e U).hom ((coordinates M S e U).inv s))
  rw [Iso.inv_hom_id_apply]

/-- The original degree inclusion, extended as a linear map on all opens. -/
def ι (n : ℕ) : M n ⟶ S :=
  AffineBasisModuleMorphism.extend (M n) S (AffineBasisDirectSum.ι M n ≫ e.inv) (by
    intro U r s
    change e.inv.hom.app (.op U) (DirectSum.of (fun k ↦ Γ(M k, U.1)) n (r • s)) = _
    rw [DirectSum.of_smul, inv_smul M S e he]
    rfl)

/-- The global inclusion retains precisely the original affine degree coordinate. -/
lemma ι_app (n : ℕ) (U : X.affineOpens) (s : Γ(M n, U.1)) :
    (ι M S e he n).app U.1 s =
      e.inv.hom.app (.op U) (DirectSum.of (fun k ↦ Γ(M k, U.1)) n s) :=
  ConcreteCategory.congr_hom (AffineBasisModuleMorphism.extend_app _ _ _ _ U) s

/-- A family of original module maps extends by finite addition in affine coordinates. -/
def desc {N : X.Modules} (a : ∀ n, M n ⟶ N) : S ⟶ N :=
  AffineBasisModuleMorphism.extend S N (e.hom ≫ AffineBasisDirectSum.desc M a) (by
    intro U r s
    change DirectSum.toAddMonoid (fun n ↦ (a n).app U.1 |>.hom)
        (e.hom.hom.app (.op U) (r • s)) = _
    rw [he]
    exact (DirectSum.toModule Γ(X, U.1) ℕ Γ(N, U.1)
      (fun n ↦ { (a n).app U.1 |>.hom with
        map_smul' := fun r s ↦ (a n).app_smul r s })).map_smul r _)

/-- Descent on affine sections is the original finite sum of degreewise maps. -/
lemma desc_app {N : X.Modules} (a : ∀ n, M n ⟶ N)
    (U : X.affineOpens) (s : Γ(S, U.1)) :
    (desc M S e he a).app U.1 s =
      DirectSum.toAddMonoid (fun n ↦ (a n).app U.1 |>.hom) (e.hom.hom.app (.op U) s) :=
  ConcreteCategory.congr_hom (AffineBasisModuleMorphism.extend_app _ _ _ _ U) s

end FLT.Mazur.AffineBasisSumMaps
