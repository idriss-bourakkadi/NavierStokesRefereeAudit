/-
Copyright (c) 2026 Mr. Driss Bourakkadi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mr. Driss Bourakkadi
-/
import NavierStokesRefereeAudit.Layer0_CoreDefinitions
import NavierStokesRefereeAudit.Layer1_BaselineOperators
import NavierStokesRefereeAudit.Layer2_PrescriptiveFormulation
import NavierStokesRefereeAudit.Layer3_TeleologicalSinksCollapse
import NavierStokesRefereeAudit.Layer4_BackgroundDivergence
import NavierStokesRefereeAudit.Layer5_IterationDivergenceBorel
import NavierStokesRefereeAudit.Layer6_ParameterHierarchyCorrugation
import NavierStokesRefereeAudit.Layer7_UniquenessAndBenchmarks
import NavierStokesRefereeAudit.Layer8_MillenniumQuantifierLogic

/-!
# Navier-Stokes Referee Audit Formalization: Root Library

This is the top-level aggregator module for the `NavierStokesRefereeAudit` Lean 4 formalization.
It re-exports all 9 formalization layers (Layers 0 through 8), encompassing the complete
semantic mapping ledger (Equations 1–165) for the referee report:
`Report on OpenAI Paper "Finite Time Blowup for Navier-Stokes" and Accompanying Lean 4 Formalization`
(oainspr_manuscript_v1.1.0, November 05, 2026).
-/
