/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisSumMaps

/-!
# Recognizing the global sheaf coproduct from affine coordinates

Natural, structure-linear coordinates in the original affine degree sums
identify an actual module sheaf with the categorical coproduct of those degrees.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Scheme.Modules
open scoped DirectSum

universe u

namespace FLT.Mazur.AffineBasisSumMaps

variable {X : Scheme.{u}} (M : ℕ → X.Modules) (S : X.Modules)
  (e : AffineBasisModuleMorphism.basis S ≅ AffineBasisDirectSum.sum M)
  (he : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (s : Γ(S, U.1)),
    e.hom.hom.app (.op U) (r • s) = r •
      (show ⨁ n, Γ(M n, U.1) from e.hom.hom.app (.op U) s))

/-- The global finite-sum extension restricts to the prescribed map in each degree. -/
lemma ι_desc {N : X.Modules} (a : ∀ n, M n ⟶ N) (n : ℕ) :
    ι M S e he n ≫ desc M S e he a = a n := by
  apply AffineBasisModuleMorphism.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  change (desc M S e he a).app U.1 ((ι M S e he n).app U.1 s) = _
  rw [ι_app, desc_app]
  change DirectSum.toAddMonoid (fun k ↦ (a k).app U.1 |>.hom)
      ((coordinates M S e U).hom
        ((coordinates M S e U).inv (DirectSum.of (fun k ↦ Γ(M k, U.1)) n s))) = _
  rw [Iso.inv_hom_id_apply, DirectSum.toAddMonoid_of]

/-- The original degree inclusions jointly determine every global module map. -/
lemma hom_ext {N : X.Modules} {a b : S ⟶ N}
    (h : ∀ n, ι M S e he n ≫ a = ι M S e he n ≫ b) : a = b := by
  apply AffineBasisModuleMorphism.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  have hs (t : ⨁ n, Γ(M n, U.1)) :
      a.app U.1 ((coordinates M S e U).inv t) =
        b.app U.1 ((coordinates M S e U).inv t) := by
    induction t using DirectSum.induction_on with
    | zero => simp
    | of n t =>
        have hh := ConcreteCategory.congr_hom (congrArg (fun k ↦ k.app U.1) (h n)) t
        change a.app U.1 ((ι M S e he n).app U.1 t) =
          b.app U.1 ((ι M S e he n).app U.1 t) at hh
        rw [ι_app] at hh
        exact hh
    | add t v ht hv => simpa only [map_add] using congrArg₂ (· + ·) ht hv
  simpa only [Iso.hom_inv_id_apply] using hs ((coordinates M S e U).hom s)

/-- The actual global sheaf, with its original degree maps, is a coproduct. -/
def isColimit : IsColimit (Cofan.mk S (ι M S e he)) :=
  Cofan.IsColimit.mk _ (fun c ↦ desc M S e he c.inj)
    (fun c n ↦ ι_desc M S e he c.inj n)
    (fun c _ ha ↦ hom_ext M S e he (fun n ↦ (ha n).trans (ι_desc M S e he c.inj n).symm))

/-- The global identification with the sheaf coproduct of the original degrees. -/
def coproductIso : S ≅ ∐ M :=
  (isColimit M S e he).coconePointUniqueUpToIso (coproductIsCoproduct M)

/-- The global isomorphism carries the original degree maps to coproduct injections. -/
lemma ι_coproductIso_hom (n : ℕ) :
    ι M S e he n ≫ (coproductIso M S e he).hom = Sigma.ι M n :=
  (isColimit M S e he).comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct M) ⟨n⟩

end FLT.Mazur.AffineBasisSumMaps
