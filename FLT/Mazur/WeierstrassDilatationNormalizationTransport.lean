/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationCanonicalNormalizationNaturality
public import FLT.Mazur.WeierstrassDilatationCoefficientTransport

/-!
# Full normalization with explicitly identified target coefficients

Transporting coefficient equalities before constructing the square avoids
large definitional reductions in arithmetic quotient applications.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
attribute [local irreducible] terminalTangentRoot terminalSmoothing terminalNodeEquiv
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (U : WeierstrassCurve S) (t c3 c4 c6 : S)
  (hW : W.map f = U) (hst : f s = t) (h3 : f b3 = c3)
  (h4c : f b4 = c4) (h6c : f b6 = c6)
  (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (hf : I ≤ J.comap f) (ha : IsUnit W.a₁)
  (hs : s ∈ I) (h2 : W.a₂ ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
  (ha' : IsUnit U.a₁) (ht : t ∈ J) (h2' : U.a₂ ∈ J) (h4' : c4 ∈ J) (h6' : c6 ∈ J)
local notation "r" => terminalTangentRoot W s I hI ha hs h2
local notation "r'" => terminalTangentRoot U t J hJ ha' ht h2'
local notation "hrI" => terminalTangentRoot_mem W s I hI ha hs h2
local notation "hrJ" => terminalTangentRoot_mem U t J hJ ha' ht h2'
local notation "c" => terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6
local notation "d" => terminalSmoothing U c3 c4 c6 r' J hJ hrJ ha' h4' h6'
local notation "e" => canonicalTerminalNodeEquiv W s b3 b4 b6 I hI ha h4 h6 hs h2
local notation "e'" => canonicalTerminalNodeEquiv U t c3 c4 c6 J hJ ha' h4' h6' ht h2'
local notation "g" => coefficientRingMapTo f W s b3 b4 b6 U t c3 c4 c6 hW hst h3 h4c h6c

include hW hst h3 h4c h6c hf in
/-- Explicitly identified target coefficients preserve the actual constructed smoothing. -/
theorem canonicalTerminalSmoothing_transport : f c = d := by
  subst U t c3 c4 c6
  exact canonicalTerminalSmoothing_map f W s b3 b4 b6 I hI J hJ hf ha hs h2 h4 h6

local notation "hc" => canonicalTerminalSmoothing_transport f W s b3 b4 b6 U t c3 c4 c6
  hW hst h3 h4c h6c I hI J hJ hf ha hs h2 h4 h6 ha' ht h2' h4' h6'
local notation "N" => NodalFiber.coefficientRingMap f c d hc

/-- The full inverse normalization commutes after explicit coefficient identification. -/
theorem canonicalTerminalNodeEquiv_symm_transport :
    (g).comp (e).symm.toAlgHom.toRingHom = (e').symm.toAlgHom.toRingHom.comp N := by
  subst U t c3 c4 c6
  exact canonicalTerminalNodeEquiv_symm_map f W s b3 b4 b6 I hI J hJ hf ha hs h2 h4 h6

/-- The full forward normalization commutes after the same explicit identification. -/
theorem canonicalTerminalNodeEquiv_transport :
    (e').toAlgHom.toRingHom.comp g = (N).comp (e).toAlgHom.toRingHom := by
  subst U t c3 c4 c6
  exact canonicalTerminalNodeEquiv_map f W s b3 b4 b6 I hI J hJ hf ha hs h2 h4 h6

end FLT.Mazur.WeierstrassDilatation
