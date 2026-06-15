/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/
import Oseledets.MultiplicativeErgodic
import Oseledets.Lyapunov.Corollaries

/-!
# Axiom audit

A guarded audit that the target theorem `Oseledets.oseledets_filtration` and its companion
corollaries depend only on Lean/Mathlib's three standard axioms `propext`, `Classical.choice`,
`Quot.sound` — in particular on no `sorryAx` and no extra axioms.

Each `#guard_msgs in #print axioms` block below compares the declaration's axiom set against
the expected `[propext, Classical.choice, Quot.sound]` and **fails the build if it ever
differs**, so this module is a continuously-checked regression test rather than an
informational dump (it produces no output on success).
-/

/-- info: 'Oseledets.oseledets_filtration' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledets_filtration

/-- info: 'Oseledets.oseledets_filtration'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledets_filtration'

/-- info: 'Oseledets.oseledets_top_exponent_eq_furstenbergKesten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledets_top_exponent_eq_furstenbergKesten

/-- info: 'Oseledets.oseledets_filtration_with_multiplicities' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.oseledets_filtration_with_multiplicities

/-- info: 'Oseledets.IsOseledetsFiltration.ae_mem_iff_limsup_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.ae_mem_iff_limsup_le

/-- info: 'Oseledets.IsOseledetsFiltration.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.unique

/-- info: 'Oseledets.IsOseledetsFiltration.tendsto_log_opNorm_cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.tendsto_log_opNorm_cocycle

/-- info: 'Oseledets.IsOseledetsFiltration.exists_finrank_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.exists_finrank_ae_eq

/-- info: 'Oseledets.IsOseledetsFiltration.exists_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Oseledets.IsOseledetsFiltration.exists_multiplicity
