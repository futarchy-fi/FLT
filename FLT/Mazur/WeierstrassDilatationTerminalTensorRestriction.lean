/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTerminalRestriction
public import FLT.Mazur.WeierstrassDilatationTerminalTensorNode

/-!
# Full terminal node restriction on original tensor-valued maps

Restriction through the tensor equivalence recovers all original functions.
The two coordinates are the explicitly constructed factors in the divided cubic.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
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
local notation "T₀" => ScalarExtension W s b3 b4 b6 S
local notation "c" => terminalSmoothing U (q b3) (q b4) (q b6) r I hI hrI ha h4 h6
local notation "N" => NodalFiber.Coordinate c
local notation "e" => tensorTerminalNodeEquiv W s b3 b4 b6 S r I hI hrI ha h4 h6 hr
variable {B : Type u} [CommRing B] [Algebra S B]
  (g : ScalarExtension W s b3 b4 b6 S →ₐ[S] B)

/-- The complete terminal node map induced by a map of the original tensor chart. -/
def tensorTerminalNodeRestriction : N →ₐ[S] B := g.comp (e).symm.toAlgHom

/-- Both full tensor boundary restrictions commute on every original function. -/
theorem tensorTerminalNodeRestriction_comp :
    (tensorTerminalNodeRestriction W s b3 b4 b6 S r I hI hrI ha h4 h6 hr g).comp
      (e).toAlgHom = g := by
  apply AlgHom.ext
  intro z
  exact congrArg g ((e).symm_apply_apply z)

/-- The first restricted coordinate is the original explicit tensor factor. -/
theorem tensorTerminalNodeRestriction_p :
    tensorTerminalNodeRestriction W s b3 b4 b6 S r I hI hrI ha h4 h6 hr g (NodalFiber.p c) =
      g (baseChangeBackward W s b3 b4 b6 S
        (terminalNodeSmall U (q s) (q b3) (q b4) (q b6) r I hI hrI ha h4 h6)) := by
  change g (baseChangeBackward W s b3 b4 b6 S
    ((terminalNodeEquiv U (q s) (q b3) (q b4) (q b6) r I hI hrI ha h4 h6 hr).symm
      (NodalFiber.p c))) = _
  rw [terminalNodeEquiv_symm_p]

/-- The opposite restricted coordinate is the original explicit tensor factor. -/
theorem tensorTerminalNodeRestriction_q :
    tensorTerminalNodeRestriction W s b3 b4 b6 S r I hI hrI ha h4 h6 hr g (NodalFiber.q c) =
      g (baseChangeBackward W s b3 b4 b6 S
        (terminalNodeOpposite U (q s) (q b3) (q b4) (q b6) r I hI hrI ha h4 h6)) := by
  change g (baseChangeBackward W s b3 b4 b6 S
    ((terminalNodeEquiv U (q s) (q b3) (q b4) (q b6) r I hI hrI ha h4 h6 hr).symm
      (NodalFiber.q c))) = _
  rw [terminalNodeEquiv_symm_q]

/-- The complete node restriction commutes with the original tensor morphism on spectra. -/
@[reassoc] theorem tensorTerminalNodeRestriction_spec :
    Spec.map (CommRingCat.ofHom
      (tensorTerminalNodeRestriction W s b3 b4 b6 S r I hI hrI ha h4 h6 hr g).toRingHom) ≫
        (tensorTerminalNodeIso W s b3 b4 b6 S r I hI hrI ha h4 h6 hr).hom =
          Spec.map (CommRingCat.ofHom g.toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  exact congrArg (fun f : T₀ →ₐ[S] B ↦ Spec.map (CommRingCat.ofHom f.toRingHom))
    (tensorTerminalNodeRestriction_comp W s b3 b4 b6 S r I hI hrI ha h4 h6 hr g)

end FLT.Mazur.WeierstrassDilatation
