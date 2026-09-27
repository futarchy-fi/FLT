/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib
import FLT

/-!
Check that no FLT declarations conflict with Mathlib.
-/

-- The unrestricted proof escape hatch must no longer be available.
/-- error: Unknown identifier `knownin1980s` -/
#guard_msgs in
#check knownin1980s
