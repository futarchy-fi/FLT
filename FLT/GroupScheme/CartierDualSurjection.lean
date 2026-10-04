/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.CartierDualFaithfullyFlat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-! # Faithful flatness of the transpose over the actual integral base -/

@[expose] public noncomputable section
namespace HopfAlgebra.CartierDual
variable {R A B : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [CommRing A] [CommRing B] [HopfAlgebra R A] [HopfAlgebra R B]
  [Coalgebra.IsCocomm R A] [Coalgebra.IsCocomm R B]
  [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]

omit [IsDomain R] [IsPrincipalIdealRing R] [Coalgebra.IsCocomm R A]
  [Coalgebra.IsCocomm R B] in
/-- The transpose of a surjective finite projective Hopf map is injective. -/
theorem bialgMap_injective_of_surjective (f : A →ₐc[R] B)
    (hf : Function.Surjective f) : Function.Injective (bialgMap f) := by
  intro φ ψ h
  apply WithConv.ext
  ext b
  obtain ⟨a, rfl⟩ := hf b
  exact congrArg (fun χ : CartierDual R A ↦ χ a) h

/-- A surjective coordinate map transposes to a faithfully flat coordinate map. -/
theorem bialgMap_faithfullyFlat_of_surjective (f : A →ₐc[R] B)
    (hf : Function.Surjective f) : (bialgMap f).toAlgHom.toRingHom.FaithfullyFlat := by
  let := (bialgMap f).toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R (CartierDual R B) (CartierDual R A) :=
    IsScalarTower.of_algHom (bialgMap f).toAlgHom
  exact HopfAlgebra.faithfullyFlat_of_injective_residueBaseChange (bialgMap f) rfl
    (bialgMap_injective_of_surjective f hf)
    (fun I _ ↦ bialgMap_lTensor_injective f hf (R ⧸ I))

end HopfAlgebra.CartierDual
