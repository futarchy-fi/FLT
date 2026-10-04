/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.RootUniformizerModel
public import FLT.AbsoluteGaloisGroup.TameCharacterSurjective

/-!
# An integral model containing the specified tame root

Apply the binomial construction to the exact root used by tameCharacter.
The root equation and irreducibility are outputs. Normality and comparison
with arbitrary finite character models are not assumed or asserted.
-/

@[expose] public noncomputable section
open NumberField IsLocalRing
universe u
variable {K : Type u} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The specific base element chosen for the tame character is irreducible. -/
theorem tameUniformizer_irreducible : Irreducible (tameUniformizer v) := by
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  exact IsDedekindDomain.HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer
    K v (tameUniformizer_spec v)

/-- The exact chosen tame root lies in a constructed finite DVR as its uniformizer. -/
theorem tameRoot_exists_integral_model :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsDiscreteValuationRing S)
      (_ : Algebra (v.adicCompletionIntegers K) S)
      (_ : Module.Finite (v.adicCompletionIntegers K) S) (y : S)
      (f : S →ₐ[v.adicCompletionIntegers K] AlgebraicClosure (v.adicCompletion K)),
      Irreducible y ∧
        y ^ (Nat.card (ResidueField (v.adicCompletionIntegers K)) - 1) =
          algebraMap (v.adicCompletionIntegers K) S (tameUniformizer v) ∧
        f y = tameUniformizerRoot v ∧ Function.Injective f ∧
        Algebra.adjoin (v.adicCompletionIntegers K) {y} = ⊤ := by
  exact LocalRoot.exists_embedded_root_uniformizer_model
    (AlgebraicClosure (v.adicCompletion K)) (tameUniformizer_irreducible v)
    (tameDegree_pos v) (tameUniformizerRoot_spec v)
