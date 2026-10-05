/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.SerreWeight.CoefficientCharacterExponent
public import FLT.GaloisRepresentation.SerreWeight.OrdinaryBranch

/-!
# Ordinary recipe inputs over general coefficient fields

Extract the normalized prime-field exponent and the independent whole-local
branch from an ordinary filtration over any coefficient field. Kernel
containment and surjectivity of the original inertia character remain explicit
arithmetic obligations. This does not assert a numerical Serre weight.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation.Extensions.OrdinaryFiltration
open SerreWeight SerreWeightRecipe
variable {G k V : Type*} [Group G] [Field k] {p : ℕ} [Fact p.Prime]
  [AddCommGroup V] [Module k V]
  [TopologicalSpace G] [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace V] [DiscreteTopology V]
  {ρ : Representation k G V} {α β : G →* kˣ}
  (E : OrdinaryFiltration ρ α β) (hρ : ∀ x : V, Continuous (fun g ↦ ρ g x))
  (f : ZMod p →+* k) (I : Subgroup G) (ε : G →* (ZMod p)ˣ)
  (hε : Function.Surjective (ε.comp I.subtype))
  (hker : (ε.comp I.subtype).ker ≤ ((homCharacter α β).comp I.subtype).ker)

/-- The recipe input is extracted over the given coefficient field and original inertia. -/
def coefficientOrdinaryInput : ReducibleInput p where
  exponent := coefficientCharacterExponent f (ε.comp I.subtype)
    ((homCharacter α β).comp I.subtype) hε hker
  lower := (coefficientCharacterExponent_spec f _ _ hε hker).1
  upper := (coefficientCharacterExponent_spec f _ _ hε hker).2.1
  extensionCase := E.ordinaryBranch hρ I ((Units.map f.toMonoidHom).comp ε)
  exceptionalExponent := by
    intro ht
    have he := ((E.ordinaryBranch_tres_iff hρ I ((Units.map f.toMonoidHom).comp ε)).mp ht).1
    have hc : (homCharacter α β).comp I.subtype =
        (Units.map f.toMonoidHom).comp (ε.comp I.subtype) := by rw [he]; rfl
    simp only [hc] at hker ⊢
    exact coefficientCharacterExponent_self f _ hε hker

/-- The selected exponent recovers the Hom character on the specified inertia group. -/
theorem coefficientOrdinaryInput_character (g : I) :
    homCharacter α β g = Units.map f.toMonoidHom (ε g) ^
      (E.coefficientOrdinaryInput hρ f I ε hε hker).exponent :=
  (coefficientCharacterExponent_spec f _ _ hε hker).2.2 g

/-- The constructed input uses actual equivariant splitting for its split branch. -/
theorem coefficientOrdinaryInput_split_iff :
    (E.coefficientOrdinaryInput hρ f I ε hε hker).extensionCase = .split ↔ E.Splits :=
  E.ordinaryBranch_split_iff hρ I _

/-- The exceptional branch keeps the whole-local character test and independent non-peu class. -/
theorem coefficientOrdinaryInput_tres_iff :
    (E.coefficientOrdinaryInput hρ f I ε hε hker).extensionCase = .cyclotomicTres ↔
      homCharacter α β = (Units.map f.toMonoidHom).comp ε ∧ ¬ E.IsPeu hρ I :=
  E.ordinaryBranch_tres_iff hρ I _

end GaloisRepresentation.Extensions.OrdinaryFiltration
