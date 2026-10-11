/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineAlgebraDescentReconstruction

/-!
# Effective descent of compatible algebra morphisms

A map compatible with the original coactions restricts to the constructed
fixed rings. Its scalar extension recovers the original algebra map under
the specified reconstructions. Identity and composition hold literally.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.AffineAlgebraDescent
universe u
variable {R S B C E : Type u} [CommRing R] [CommRing S] [CommRing B]
  [CommRing C] [CommRing E] [Algebra R S]
  [Algebra R B] [Algebra S B] [IsScalarTower R S B]
  [Algebra R C] [Algebra S C] [IsScalarTower R S C]
  [Algebra R E] [Algebra S E] [IsScalarTower R S E]
  (D : Data R S B) (D' : Data R S C) (D'' : Data R S E)

/-- Compatibility with the supplied multiplicative descent coactions. -/
def Compatible (h : B →ₐ[S] C) : Prop :=
  ∀ b, D'.coaction (h b) = (h.toLinearMap.restrictScalars R).lTensor S (D.coaction b)

/-- A compatible original map restricts to the actual fixed coordinate rings. -/
def descendMap (h : B →ₐ[S] C) (hh : Compatible D D' h) :
    invariants D →ₐ[R] invariants D' :=
  ((h.restrictScalars R).comp (invariants D).val).codRestrict (invariants D') (by
    intro b
    rw [mem_invariants]
    change D'.coaction (h b.val) = 1 ⊗ₜ[R] h b.val
    rw [hh, (mem_invariants D b.val).mp b.property]
    rfl)

/-- The descended map retains every original fixed coefficient. -/
theorem descendMap_val (h : B →ₐ[S] C) (hh : Compatible D D' h) (b : invariants D) :
    (descendMap D D' h hh b).val = h b.val := rfl

/-- The actual scalar extension of the descended algebra map. -/
def extendedMap (h : B →ₐ[S] C) (hh : Compatible D D' h) :
    S ⊗[R] invariants D →ₐ[S] S ⊗[R] invariants D' :=
  AlgHom.liftEquiv R S _ _ (Algebra.TensorProduct.includeRight.comp (descendMap D D' h hh))

/-- Reconstruction recovers the original coefficient map on the entire scalar extension. -/
theorem reconstruct_naturality (h : B →ₐ[S] C) (hh : Compatible D D' h) :
    (reconstruct D').comp (extendedMap D D' h hh) = h.comp (reconstruct D) := by
  apply AlgHom.toLinearMap_injective
  apply AlgebraTensorModule.ext
  intro s b
  change reconstruct D' (s • ((1 : S) ⊗ₜ[R] descendMap D D' h hh b)) = h (s • b.val)
  rw [map_smul, reconstruct_tmul, one_smul, descendMap_val, map_smul]

/-- Descending the identity gives the identity on the constructed coordinate ring. -/
theorem descendMap_id (hh : Compatible D D (AlgHom.id S B)) :
    descendMap D D (AlgHom.id S B) hh = AlgHom.id R (invariants D) := by
  ext b
  rfl

/-- Composing compatible original maps composes their actual descended maps. -/
theorem descendMap_comp (h : B →ₐ[S] C) (k : C →ₐ[S] E)
    (hh : Compatible D D' h) (hk : Compatible D' D'' k)
    (hkh : Compatible D D'' (k.comp h)) :
    descendMap D D'' (k.comp h) hkh =
      (descendMap D' D'' k hk).comp (descendMap D D' h hh) := by
  ext b
  rfl

/-- The inclusion formula determines the descended map uniquely. -/
theorem descendMap_unique (h : B →ₐ[S] C) (hh : Compatible D D' h)
    (g : invariants D →ₐ[R] invariants D')
    (hg : ∀ b, (g b).val = h b.val) : g = descendMap D D' h hh := by
  ext b
  exact hg b

end FLT.Mazur.AffineAlgebraDescent
