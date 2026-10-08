/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ReesModuleBaseChange
public import FLT.Mazur.AffineCoherent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.FiniteStability

/-!
# Coherent affine models for the actual Rees modules

The extended-ideal Rees spectrum is a closed subscheme of the relative
spectrum. The actual power module defines a coherent sheaf on that relative
spectrum. Gluing these affine models and comparing cohomology remain separate.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve
open scoped TensorProduct

universe u

namespace FLT.Mazur.Rees

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)

/-- The actual extended-ideal Rees spectrum inside the affine scalar extension. -/
def affineClosedMap :
    Spec (.of (reesAlgebra (I.map (Algebra.algebraMap R S)))) ⟶
      Spec (.of (S ⊗[R] reesAlgebra I)) :=
  Spec.map (CommRingCat.ofHom (relativeMap (S := S) I).toRingHom)

/-- The proved relative Rees surjection gives the actual closed immersion. -/
instance affineClosedMap_isClosedImmersion : IsClosedImmersion (affineClosedMap (S := S) I) :=
  IsClosedImmersion.spec_of_surjective _ (relativeMap_surjective I)

variable [IsNoetherianRing R] [IsNoetherianRing S]

/-- The relative affine coordinate ring is Noetherian over the original chart ring. -/
theorem relativeRing_noetherian : IsNoetherianRing (S ⊗[R] reesAlgebra I) :=
  Algebra.FiniteType.isNoetherianRing S _

variable (M : Type u) [AddCommGroup M] [Module S M] [Module.Finite S M]

/-- The sheaf on the relative spectrum associated to the actual ideal-power module. -/
def affineModuleSheaf : (Spec (.of (S ⊗[R] reesAlgebra I))).Modules := by
  let _ := relativeModule (S := S) (M := M) I
  exact tilde (ModuleCat.of (S ⊗[R] reesAlgebra I) (extendedModule (S := S) (M := M) I))

/-- Finiteness of the actual relative module gives coherence of its affine model. -/
instance affineModuleSheaf_isFinitePresentation :
    (affineModuleSheaf (S := S) I M).IsFinitePresentation := by
  let _ := relativeModule (S := S) (M := M) I
  let _ := relativeRing_noetherian (S := S) I
  let _ := relativeModule_finite (S := S) (M := M) I
  exact affineTilde_isFinitePresentation_of_finite (R := .of (S ⊗[R] reesAlgebra I))
    (ModuleCat.of (S ⊗[R] reesAlgebra I) (extendedModule (S := S) (M := M) I))

end FLT.Mazur.Rees
