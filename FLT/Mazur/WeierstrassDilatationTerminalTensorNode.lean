/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationBaseChange
public import FLT.Mazur.WeierstrassDilatationTerminalNodeCoordinates
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The full terminal node on the original arithmetic tensor scheme

The original base-change equivalence transports the constructed full node,
preserving every original function and the arithmetic coefficient morphism.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDilatation
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (S : Type u) [CommRing S] [Algebra R S]
  (r : S[X]) (I : Ideal S) (hI : IsNilpotent I) (hrI : r ∈ I.map C)
  (ha : IsUnit (W.map (algebraMap R S)).a₁)
  (h4 : algebraMap R S b4 ∈ I) (h6 : algebraMap R S b6 ∈ I)
  (hr : r ^ 2 + C (W.map (algebraMap R S)).a₁ * r =
    C (W.map (algebraMap R S)).a₂ + C (algebraMap R S s) * X)
local notation "q" => algebraMap R S
local notation "U" => W.map q
local notation "T" => ScalarExtension W s b3 b4 b6 S
local notation "c" => terminalSmoothing U (q b3) (q b4) (q b6) r I hI hrI ha h4 h6
local notation "N" => NodalFiber.Coordinate c
local notation "e" => terminalNodeEquiv U (q s) (q b3) (q b4) (q b6) r I hI hrI ha h4 h6 hr

/-- The whole original arithmetic tensor algebra is the computed terminal smoothing node. -/
def tensorTerminalNodeEquiv : T ≃ₐ[S] N := (baseChangeEquiv W s b3 b4 b6 S).trans e

/-- The tensor comparison preserves each original function with its actual coefficient map. -/
theorem tensorTerminalNodeEquiv_tmul (a : S) (z : Coordinate W s b3 b4 b6) :
    tensorTerminalNodeEquiv W s b3 b4 b6 S r I hI hrI ha h4 h6 hr (a ⊗ₜ[R] z) =
      a • e (coefficientMap W s b3 b4 b6 S z) := by
  change e (baseChangeForward W s b3 b4 b6 S (a ⊗ₜ[R] z)) = _
  rw [baseChangeForward_tmul, map_smul]

/-- The complete smoothing node is isomorphic to the original terminal tensor scheme. -/
def tensorTerminalNodeIso : Spec (.of N) ≅ Spec (.of T) :=
  Scheme.Spec.mapIso
    (tensorTerminalNodeEquiv W s b3 b4 b6 S r I hI hrI ha h4 h6 hr).toRingEquiv.toCommRingCatIso.op

/-- The full tensor node comparison preserves its arithmetic coefficient morphism. -/
@[reassoc] theorem tensorTerminalNodeIso_structure :
    (tensorTerminalNodeIso W s b3 b4 b6 S r I hI hrI ha h4 h6 hr).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap S T)) =
        Spec.map (CommRingCat.ofHom (algebraMap S N)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (tensorTerminalNodeEquiv W s b3 b4 b6 S r I hI hrI ha h4 h6 hr).commutes z

end FLT.Mazur.WeierstrassDilatation
