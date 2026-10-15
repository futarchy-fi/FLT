/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationInverseNaturality
public import FLT.Mazur.DifferenceNodeCriticalNaturality
public import FLT.Mazur.WeierstrassDilatationTerminalNode

/-!
# The actual terminal smoothing constant commutes with coefficient maps

This compares the constructed inverse, retained product correction and
critical point. Compatibility of the smoothing constants is proved, not assumed.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (b3 b4 b6 : R) (r : R[X])
  (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (hf : I ≤ J.comap f) (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
  (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "F" => terminalInversePolynomial W r I hI hrI ha
local notation "H" => terminalProductCorrection b3 b4 b6 r F
local notation "hH" => terminalProductCorrection_mem b3 b4 b6 r F I h4 h6 hrI
local notation "hrJ" => terminalPolynomialIdeal_map f I J hf hrI

/-- The full terminal smoothing is functorial for every ideal-preserving coefficient map. -/
theorem terminalSmoothing_map :
    f (terminalSmoothing W b3 b4 b6 r I hI hrI ha h4 h6) =
      terminalSmoothing (W.map f) (f b3) (f b4) (f b6) (r.map f)
        J hJ hrJ (ha.map f) (hf h4) (hf h6) := by
  have h := DifferenceNode.smoothingConstant_map f H b3 I hI J hJ hf hH
  simpa only [terminalSmoothing,
    terminalConstructedCorrection_map f W r I hI J hJ hf hrI ha b3 b4 b6] using h

end FLT.Mazur.WeierstrassDilatation
