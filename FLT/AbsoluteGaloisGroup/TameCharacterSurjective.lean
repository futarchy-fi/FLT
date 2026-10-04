/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FundamentalTame

/-!
# Surjectivity of the specified absolute tame character

Identify the chosen level-one character with the existing reduced root
character. Inertia transitivity then proves surjectivity for that exact
character, including residue field cardinality two.
-/

@[expose] public noncomputable section
open NumberField IsLocalRing
variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The chosen tame root gives exactly the reduced root character used for inertia transitivity. -/
theorem reducedKummerCharacter_eq_rootCharacter :
    reducedKummerCharacter v = LocalRoot.rootCharacterToRoots v (tameDegree_pos v)
      (tameUniformizer_spec v) (tameUniformizerRoot_spec v) := by
  ext σ
  rfl

/-- Absolute inertia surjects onto the units of the completion's actual residue field. -/
theorem tameCharacter_surjective : Function.Surjective (tameCharacter v) := by
  unfold tameCharacter
  apply (residueUnitsEquivRoots v).symm.surjective.comp
  rw [reducedKummerCharacter_eq_rootCharacter]
  exact LocalRoot.rootCharacterToRoots_surjective v (tameDegree_pos v)
    (tameUniformizer_spec v) (tameUniformizerRoot_spec v)

/-- The kernel quotient of the specified character is the full residue unit group. -/
def tameCharacterQuotientEquiv :
    localInertiaGroup v ⧸ (tameCharacter v).ker ≃*
      (ResidueField (v.adicCompletionIntegers K))ˣ :=
  QuotientGroup.quotientKerEquivOfSurjective (tameCharacter v) (tameCharacter_surjective v)

/-- Every residue unit is attained by the specified character, with its original normalization. -/
theorem tameCharacterQuotientEquiv_mk (σ : localInertiaGroup v) :
    tameCharacterQuotientEquiv v (QuotientGroup.mk σ) = tameCharacter v σ := rfl

/-- Any normalized level-one root computes the specified tame character after residue inclusion. -/
theorem tameCharacter_residue_eq_rootCharacter
    {π : v.adicCompletionIntegers K}
    (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : AlgebraicClosure (v.adicCompletion K)}
    (hα : α ^ (Nat.card (ResidueField (v.adicCompletionIntegers K)) - 1) =
      algebraMap (v.adicCompletion K) (AlgebraicClosure (v.adicCompletion K)) π.1)
    (σ : localInertiaGroup v) :
    residueFieldMap v (tameCharacter v σ : ResidueField (v.adicCompletionIntegers K)) =
      (LocalRoot.character v (tameDegree_pos v)
        (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
          hπ (Subtype.ext h)) hα σ :
            ResidueField (IntegralClosure (v.adicCompletionIntegers K)
              (AlgebraicClosure (v.adicCompletion K)))) := by
  rw [tameCharacter_uniformizer_independent v hπ hα]
  have h := congrArg (fun z ↦ (z.1 : ResidueField
    (IntegralClosure (v.adicCompletionIntegers K) (AlgebraicClosure (v.adicCompletion K)))))
    ((residueUnitsEquivRoots v).apply_symm_apply
      (reducedKummerRatioOfRoot v
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero hπ) hα σ))
  exact h
