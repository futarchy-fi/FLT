/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Descending bialgebra maps through a surjective bialgebra quotient -/

@[expose] public noncomputable section
namespace BialgHom
variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

/-- An algebra factor of a bialgebra map through a surjective bialgebra map
preserves the counit and comultiplication automatically. -/
def descendAlongSurjective (q : A →ₐc[R] B) (hq : Function.Surjective q)
    (f : A →ₐc[R] C) (g : B →ₐ[R] C) (hg : g.comp q.toAlgHom = f.toAlgHom) : B →ₐc[R] C := by
  apply BialgHom.ofAlgHom g
  · apply AlgHom.ext
    intro b
    obtain ⟨a, rfl⟩ := hq b
    change Coalgebra.counit (R := R) (g (q a)) = Coalgebra.counit (R := R) (q a)
    rw [show g (q a) = f a from AlgHom.congr_fun hg a,
      CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply]
  · apply AlgHom.ext
    intro b
    obtain ⟨a, rfl⟩ := hq b
    change TensorProduct.map g.toLinearMap g.toLinearMap (Coalgebra.comul (R := R) (q a)) =
      Coalgebra.comul (R := R) (g (q a))
    rw [← CoalgHomClass.map_comp_comul_apply q, TensorProduct.map_map]
    have hl : g.toLinearMap.comp q.toLinearMap = f.toLinearMap :=
      congrArg AlgHom.toLinearMap hg
    change TensorProduct.map (g.toLinearMap.comp q.toLinearMap)
      (g.toLinearMap.comp q.toLinearMap) (Coalgebra.comul (R := R) a) = _
    rw [hl, show g (q a) = f a from AlgHom.congr_fun hg a]
    exact CoalgHomClass.map_comp_comul_apply f a

/-- The descended bialgebra morphism retains its original algebra factor. -/
@[simp] theorem descendAlongSurjective_apply (q : A →ₐc[R] B) (hq : Function.Surjective q)
    (f : A →ₐc[R] C) (g : B →ₐ[R] C) (hg : g.comp q.toAlgHom = f.toAlgHom) (b : B) :
    descendAlongSurjective q hq f g hg b = g b := rfl

end BialgHom
