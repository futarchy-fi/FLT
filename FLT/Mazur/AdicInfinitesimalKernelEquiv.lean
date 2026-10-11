/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicInfinitesimalOriginalHomotopy
public import FLT.Mazur.AdicInfinitesimalConormalFunctor

/-!
# Formal infinitesimal lifts identify kernels of original complexes

Lifts in both directions induce inverse maps on the degree-one kernels:
their composites differ from identity lifts by the explicit original
homotopies. No inverse identity is required of the lifts themselves.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.AdicInfinitesimalKernelEquiv

open AdicExtensionProjection

universe u

set_option backward.isDefEq.respectTransparency false

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (P : Algebra.Extension.{u} R A)
  (Q : Algebra.Extension.{u} R B) (I : Ideal A) (J : Ideal B)
  [IsNoetherianRing P.Ring] [IsNoetherianRing Q.Ring]
  [IsNoetherianRing A] [Module.Finite A P.CotangentSpace]
  (e : AdicCompletion I A ≃ₐ[R] AdicCompletion J B)
  (f : AdicCompletion (ideal P.infinitesimal I) P.infinitesimal.Ring →ₐ[R]
    AdicCompletion (ideal Q.infinitesimal J) Q.infinitesimal.Ring)
  (g : AdicCompletion (ideal Q.infinitesimal J) Q.infinitesimal.Ring →ₐ[R]
    AdicCompletion (ideal P.infinitesimal I) P.infinitesimal.Ring)
  (hf : ∀ x, projection Q.infinitesimal J (f x) = e.toAlgHom (projection P.infinitesimal I x))
  (hg : ∀ x, projection P.infinitesimal I (g x) = e.symm.toAlgHom (projection Q.infinitesimal J x))

/-- A genuine formal lift restricts to the kernel of the completed original differential. -/
def map : LinearMap.ker (AdicCompletion.map I P.cotangentComplex) →ₛₗ[e.toRingHom]
    LinearMap.ker (AdicCompletion.map J Q.cotangentComplex) where
  toFun x := ⟨AdicInfinitesimalOriginalChainMap.conormalMap P Q I J e.toAlgHom f hf x.val,
    by
      rw [LinearMap.mem_ker, ← AdicInfinitesimalOriginalChainMap.chainMap,
        show AdicCompletion.map I P.cotangentComplex x.val = 0 from x.property, map_zero]⟩
  map_add' x y := Subtype.ext (map_add _ x.val y.val)
  map_smul' a x := Subtype.ext (LinearMap.map_smulₛₗ _ a x.val)

/-- The kernel map retains its actual original conormal value. -/
@[simp] theorem map_val (x : LinearMap.ker (AdicCompletion.map I P.cotangentComplex)) :
    (map P Q I J e f hf x).val =
      AdicInfinitesimalOriginalChainMap.conormalMap P Q I J e.toAlgHom f hf x.val := rfl

attribute [local irreducible] map

/-- Opposite formal lifts compose to the identity on every original degree-one cycle. -/
theorem conormal_leftInverse (x : AdicCompletion I P.Cotangent)
    (hx : AdicCompletion.map I P.cotangentComplex x = 0) :
    AdicInfinitesimalOriginalChainMap.conormalMap Q P J I e.symm.toAlgHom g hg
      (AdicInfinitesimalOriginalChainMap.conormalMap P Q I J e.toAlgHom f hf x) = x := by
  have hc : ∀ y, projection P.infinitesimal I ((g.comp f) y) =
      (AlgHom.id R (AdicCompletion I A)) (projection P.infinitesimal I y) := by
    intro y
    change projection P.infinitesimal I (g (f y)) = projection P.infinitesimal I y
    rw [hg, hf]
    exact e.symm_apply_apply _
  have h := AdicInfinitesimalConormalFunctor.map_comp P Q P I J I
    e.toAlgHom e.symm.toAlgHom f g hf hg x
  have he : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id R _ := by
    exact AlgEquiv.symm_comp e
  have hbase (d : AdicCompletion I A →ₐ[R] AdicCompletion I A)
      (hd : d = AlgHom.id R _)
      (hdg : ∀ y, projection P.infinitesimal I ((g.comp f) y) =
        d (projection P.infinitesimal I y)) :
      AdicInfinitesimalOriginalChainMap.conormalMap P P I I d (g.comp f) hdg x =
        AdicInfinitesimalOriginalChainMap.conormalMap P P I I
          (AlgHom.id R _) (g.comp f) hc x := by
    subst d
    rfl
  rw [← h, hbase _ he]
  exact (AdicInfinitesimalOriginalHomotopy.conormalMap_eq_on_kernel P P I I
    (AlgHom.id R _) (g.comp f) (AlgHom.id R _) hc (fun _ ↦ rfl) x hx).trans
      (AdicInfinitesimalConormalFunctor.map_id P I x)

/-- The formal scalar equivalence and its inverse form an inverse pair. -/
local instance forwardInverse : RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e.toRingEquiv

/-- The inverse scalar equivalence has the original equivalence as inverse. -/
local instance reverseInverse : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv e.symm.toRingEquiv

variable [IsNoetherianRing B] [Module.Finite B Q.CotangentSpace]

/-- The kernel maps supplied by opposite formal lifts are mutual inverses. -/
def equiv : LinearEquiv e.toRingHom (σ' := e.symm.toRingHom)
    (LinearMap.ker (AdicCompletion.map I P.cotangentComplex))
    (LinearMap.ker (AdicCompletion.map J Q.cotangentComplex)) where
  __ := map P Q I J e f hf
  invFun := map Q P J I e.symm g hg
  left_inv := by
    intro x
    apply Subtype.ext
    change (map Q P J I e.symm g hg (map P Q I J e f hf x)).val = x.val
    rw [map_val, map_val]
    exact conormal_leftInverse P Q I J e f g hf hg x.val x.property
  right_inv := by
    intro x
    apply Subtype.ext
    change (map P Q I J e f hf (map Q P J I e.symm g hg x)).val = x.val
    rw [map_val, map_val]
    exact conormal_leftInverse Q P J I e.symm g f hg hf x.val x.property

/-- The equivalence preserves the actual original conormal map of the chosen lift. -/
@[simp] theorem equiv_val (x : LinearMap.ker (AdicCompletion.map I P.cotangentComplex)) :
    (equiv P Q I J e f g hf hg x).val =
      AdicInfinitesimalOriginalChainMap.conormalMap P Q I J e.toAlgHom f hf x.val := by
  exact map_val P Q I J e f hf x

end FLT.Mazur.AdicInfinitesimalKernelEquiv
