import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

open Filter

variable (N : Type*) [Finite N]

-- =========================================================================
-- 🌌 AXIOM A1 — Phase Primacy
-- =========================================================================
def PhaseState := N → ℝ
def Trajectory := ℝ → PhaseState N

-- Synthesize the Pi topology natively for PhaseState so Lean never throws an instance error
instance [TopologicalSpace ℝ] : TopologicalSpace (PhaseState N) := 
  Pi.topologicalSpace

-- =========================================================================
-- 🌀 AXIOM A2 — Attractor Determinism
-- =========================================================================
def AttractorSet (A : Set (PhaseState N)) : Prop :=
  ∀ (ϕ : Trajectory N), Tendsto ϕ atTop (nhdsSet A)

-- =========================================================================
-- 🛡️ AXIOM A3 — Stability over Symmetry
-- =========================================================================
def IsDynamicallyStable (lambda_max : ℝ) : Prop :=
  lambda_max < 0

-- =========================================================================
-- ⚡ AXIOM A4 — Ubiquitous Resonance
-- =========================================================================
def UbiquitousResonance (R : N → N → ℝ) : Prop :=
  ∀ i j, 0 < R i j ∧ R i j ≤ 1
