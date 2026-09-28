/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.BialgebraBaseChange
public import FLT.GroupScheme.PadicMorphismDescent

/-!
# Descent of prescribed Hopf morphisms

Arithmetic descent of algebra maps preserves the coalgebra operations when
the away map does. Consequently compatible away and local bialgebra maps
descend uniquely to the original finite projective global coordinate rings.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ThreeAdicPlan

section Reflection

variable (R S A B : Type) [CommRing R] [CommRing S] [Algebra R S]
    [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

/-- The tensor-square inclusion is scalar extension followed by tensor rearrangement. -/
theorem bialgebraScalarTensorMap_includeRight (z : B ⊗[R] B) :
    bialgebraScalarTensorMap R S B (S ⊗[R] B) Algebra.TensorProduct.includeRight z =
      (PadicPatching.tensorScalarExtensionEquiv S B).symm (1 ⊗ₜ[R] z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    apply (PadicPatching.tensorScalarExtensionEquiv S B).injective
    simp [bialgebraScalarTensorMap]
  | add x y hx hy => simp [hx, hy, TensorProduct.tmul_add]

/-- The scalar tensor inclusion commutes with comultiplication. -/
theorem bialgebraScalarTensorMap_includeRight_comul (a : A) :
    bialgebraScalarTensorMap R S A (S ⊗[R] A) Algebra.TensorProduct.includeRight
        (Coalgebra.comul (R := R) a) =
      Coalgebra.comul (R := S) (1 ⊗ₜ[R] a : S ⊗[R] A) := by
  simp only [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  generalize Coalgebra.comul (R := R) a = z
  induction z using TensorProduct.inductionOn with
  | tmul x y => simp [bialgebraScalarTensorMap]
  | add x y hx hy => simpa [TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy

/-- A global algebra map whose scalar extension is a bialgebra map preserves
both coalgebra operations. Flatness of the target makes the tensor test faithful. -/
def bialgHomOfScalarExtension [Module.Flat R B]
    (hinj : Function.Injective (algebraMap R S))
    (f : A →ₐ[R] B) (fS : S ⊗[R] A →ₐc[S] S ⊗[R] B)
    (hf : ∀ a, (1 : S) ⊗ₜ[R] f a = fS (1 ⊗ₜ[R] a)) : A →ₐc[R] B := by
  apply BialgHom.ofAlgHom f
  · ext a
    apply hinj
    have h := CoalgHomClass.counit_comp_apply fS (1 ⊗ₜ[R] a)
    rw [← hf] at h
    simpa [TensorProduct.counit_tmul, Algebra.smul_def] using h
  · ext a
    let jA := bialgebraScalarTensorMap R S A (S ⊗[R] A) Algebra.TensorProduct.includeRight
    let jB := bialgebraScalarTensorMap R S B (S ⊗[R] B) Algebra.TensorProduct.includeRight
    have hj : Function.Injective jB := by
      intro x y h
      rw [bialgebraScalarTensorMap_includeRight, bialgebraScalarTensorMap_includeRight] at h
      exact Algebra.TensorProduct.includeRight_injective hinj
        ((PadicPatching.tensorScalarExtensionEquiv S B).symm.injective h)
    apply hj
    have hmap (z : A ⊗[R] A) :
        jB (Algebra.TensorProduct.map f f z) =
          Algebra.TensorProduct.map fS.toAlgHom fS.toAlgHom (jA z) := by
      induction z using TensorProduct.inductionOn with
      | tmul x y => simp [jA, jB, bialgebraScalarTensorMap, hf]
      | add x y hx hy => simp [hx, hy]
    change jB (Algebra.TensorProduct.map f f (Coalgebra.comul (R := R) a)) =
      jB (Coalgebra.comul (R := R) (f a))
    rw [hmap, bialgebraScalarTensorMap_includeRight_comul,
      bialgebraScalarTensorMap_includeRight_comul, hf]
    exact CoalgHomClass.map_comp_comul_apply fS (1 ⊗ₜ[R] a)

end Reflection

namespace PadicPatching

variable (p : ℕ) [Fact p.Prime] (d : ℤ) [Fact (¬ (p : ℤ) ∣ d)]
    (A B : Type) [CommRing A] [CommRing B]
    [Bialgebra (Base d) A] [Bialgebra (Base d) B]
    [Module.Finite (Base d) B] [Module.Projective (Base d) B]

/-- Compatible away and local Hopf morphisms descend uniquely to the prescribed
global coordinate algebras, including the given specialization at `p`. -/
theorem existsUnique_bialgHom_of_away_local
    (fAway : Away d p ⊗[Base d] A →ₐc[Away d p] Away d p ⊗[Base d] B)
    (fLocal : ℤ_[p] ⊗[Base d] A →ₐc[ℤ_[p]] ℤ_[p] ⊗[Base d] B)
    (h : ∀ a : A,
      scalarExtensionMap (Away d p) ℚ_[p] B (fAway (1 ⊗ₜ[Base d] a)) =
        scalarExtensionMap ℤ_[p] ℚ_[p] B (fLocal (1 ⊗ₜ[Base d] a))) :
    ∃! f : A →ₐc[Base d] B,
      (∀ a, (1 : Away d p) ⊗ₜ[Base d] f a = fAway (1 ⊗ₜ[Base d] a)) ∧
      (∀ a, (1 : ℤ_[p]) ⊗ₜ[Base d] f a = fLocal (1 ⊗ₜ[Base d] a)) := by
  obtain ⟨f, hf, hu⟩ := existsUnique_algHom_of_away_local p d A B
    fAway.toAlgHom fLocal.toAlgHom h
  let F := bialgHomOfScalarExtension (Base d) (Away d p) A B
    (baseToAway_injective p d) f fAway hf.1
  refine ⟨F, hf, fun g hg ↦ ?_⟩
  have he : g.toAlgHom = f := hu g.toAlgHom hg
  ext a
  exact AlgHom.congr_fun he a


/-- A section of a prescribed integral group-scheme projection descends with its
section identity. In coordinate direction this is a left inverse to `q`. -/
theorem existsUnique_bialgHom_section_of_away_local
    (q : B →ₐc[Base d] A)
    (sAway : Away d p ⊗[Base d] A →ₐc[Away d p] Away d p ⊗[Base d] B)
    (sLocal : ℤ_[p] ⊗[Base d] A →ₐc[ℤ_[p]] ℤ_[p] ⊗[Base d] B)
    (h : ∀ a : A,
      scalarExtensionMap (Away d p) ℚ_[p] B (sAway (1 ⊗ₜ[Base d] a)) =
        scalarExtensionMap ℤ_[p] ℚ_[p] B (sLocal (1 ⊗ₜ[Base d] a)))
    (hs : sAway.comp (Bialgebra.TensorProduct.map (BialgHom.id (Away d p) (Away d p)) q) =
      BialgHom.id (Away d p) (Away d p ⊗[Base d] B)) :
    ∃! s : A →ₐc[Base d] B,
      s.comp q = BialgHom.id (Base d) B ∧
      (∀ a, (1 : Away d p) ⊗ₜ[Base d] s a = sAway (1 ⊗ₜ[Base d] a)) ∧
      (∀ a, (1 : ℤ_[p]) ⊗ₜ[Base d] s a = sLocal (1 ⊗ₜ[Base d] a)) := by
  obtain ⟨s, hs', hu⟩ := existsUnique_bialgHom_of_away_local p d A B sAway sLocal h
  refine ⟨s, ⟨?_, hs'⟩, fun t ht ↦ hu t ht.2⟩
  ext b
  apply Algebra.TensorProduct.includeRight_injective (baseToAway_injective p d)
  change (1 : Away d p) ⊗ₜ[Base d] s (q b) = 1 ⊗ₜ[Base d] b
  rw [hs'.1]
  exact congrArg (fun f : Away d p ⊗[Base d] B →ₐc[Away d p]
    Away d p ⊗[Base d] B ↦ f (1 ⊗ₜ[Base d] b)) hs

end PadicPatching
end ThreeAdicPlan
