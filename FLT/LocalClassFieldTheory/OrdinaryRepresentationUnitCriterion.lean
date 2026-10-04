/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.Extensions.OrdinaryGaloisClass
public import FLT.LocalClassFieldTheory.OrdinaryPeuUnitCriterion

/-!
# The unit criterion for an actual ordinary Galois representation

Peu ramification is defined by the independent unramified cup test on the
extracted extension class. The unit condition follows from the local theorem;
it is not a field of the filtration or the definition of peu ramification.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing NumberField KummerTheory GaloisRepresentation.Extensions
open GaloisRepresentation.Extensions.OrdinaryFiltration

variable {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

local notation "K" => v.adicCompletion F
local notation "A" => v.adicCompletionIntegers F
local notation "C" => AlgebraicClosure K

variable [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F))
    (v.adicCompletionIntegers F)]
    {k V : Type*} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [AddCommGroup V] [Module k V] [TopologicalSpace V] [DiscreteTopology V]
    [IsModuleTopology k V] (ρ : GaloisRep (v.adicCompletion F) k V)
    {α β : Field.absoluteGaloisGroup (v.adicCompletion F) →* kˣ}
    (E : OrdinaryFiltration ρ.toRepresentation α β)

/-- Peu ramification of the actual filtered representation, using cup annihilation. -/
def OrdinaryRepresentationPeuRamified : Prop :=
  IsPeuRamifiedClass (k := k) (localInertiaGroup v) (galoisClass ρ E)

/-- The independent unit criterion for the actual filtered representation. -/
theorem ordinaryRepresentationPeuRamified_iff_unit (q : ℕ) [Fact q.Prime]
    [Algebra (ZMod q) k] [FiniteDimensional (ZMod q) k]
    {ζ : Cˣ} (hζ : IsPrimitiveRoot ζ q)
    (hχ : homCharacter α β = (Units.map (algebraMap (ZMod q) k).toMonoidHom).comp
      (primeCyclotomicCharacter («K» := K) hζ)) :
    OrdinaryRepresentationPeuRamified v ρ E ↔
      OrdinaryUnitClass hζ (exists_unit_root («K» := K) (L := C) (n := q)) A
        (ordinaryHomCoordinates α β (primeCyclotomicCharacter («K» := K) hζ))
        (ordinaryHomCoordinates_equivariant α β _ hχ) (galoisClass ρ E) :=
  localOrdinaryPeuRamified_iff_unit v q hζ k α β hχ (galoisClass ρ E)

omit [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F))
  (v.adicCompletionIntegers F)] in
/-- Every section gives the same independent cup predicate. -/
theorem ordinaryRepresentationPeuRamified_iff_section (w : V) (hw : E.projection w = 1) :
    OrdinaryRepresentationPeuRamified v ρ E ↔
      IsPeuRamifiedClass (k := k) (localInertiaGroup v)
        (continuousClassMk (E.cocycleOf (continuous_galoisOrbit ρ) w hw)) := by
  unfold OrdinaryRepresentationPeuRamified
  rw [galoisClass_eq ρ E w hw]

end LocalClassFieldTheory
