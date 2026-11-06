import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

/-
Copyright (c) 2026 Mr. Driss Bourakkadi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mr. Driss Bourakkadi
-/

/-!
# Layer 0: Core Definitions, Foundational PDE Operators, and Verbatim Repository Interfaces
-/

universe u v

/-- 3D Euclidean spatial coordinates represented as Fin 3 → ℝ. -/
abbrev Space := Fin 3 → ℝ

/-- Zero vector in 3D space. -/
def zeroVec : Space := fun _ => 0

/-- Time-dependent velocity vector field u : ℝ × ℝ³ → ℝ³. -/
abbrev VelocityField := ℝ × Space → Space

/-- Time-dependent scalar pressure field p : ℝ × ℝ³ → ℝ. -/
abbrev PressureField := ℝ × Space → ℝ

/-- The pre-singular space-time domain [0, 1) × ℝ³ (Section 1.1). -/
def preSingularDomain : Set (ℝ × Space) :=
  {p | 0 ≤ p.1 ∧ p.1 < 1}

/-- The future space-time domain [0, ∞) × ℝ³. -/
def futureDomain : Set (ℝ × Space) :=
  {p | 0 ≤ p.1}

/-- Cylindrical coordinate domain: radius r > 0, height z ∈ ℝ. -/
def cylindricalDomain : Set (ℝ × ℝ) :=
  {rz | 0 < rz.1}

/-- Directional spatial advective derivative (u · ∇)u in Cartesian coordinates:
    ((u · ∇)u)ᵢ = ∑ⱼ uⱼ ∂_{xⱼ} uᵢ. -/
noncomputable def advectionTerm (u : Space) (grad_u : Fin 3 → Space → Space) : Space :=
  fun i => (u 0 * grad_u 0 u i) + (u 1 * grad_u 1 u i) + (u 2 * grad_u 2 u i)

/-- Spatial divergence ∇ · u = ∑ᵢ ∂_{xᵢ} uᵢ. -/
noncomputable def divergence (grad_u : Fin 3 → Space → Space) (u : Space) : ℝ :=
  grad_u 0 u 0 + grad_u 1 u 1 + grad_u 2 u 2

/-- Vector Laplacian Δu = ∑ᵢ ∂_{xᵢ}² u. -/
noncomputable def vectorLaplacian (d2_u : Fin 3 → Space → Space) (u : Space) : Space :=
  fun i => d2_u 0 u i + d2_u 1 u i + d2_u 2 u i

/-- Exact 3D incompressible Navier-Stokes momentum residual operator:
    ℛ_ν(u,p)(t,x) := ∂_t u + (u · ∇)u - ν Δu + ∇p (Equations 1 & 33). -/
noncomputable def navierStokesResidual (ν : ℝ) (dt_u : Space) (u : Space)
    (grad_u : Fin 3 → Space → Space) (d2_u : Fin 3 → Space → Space)
    (grad_p : Space) : Space :=
  fun i => dt_u i + advectionTerm u grad_u i - ν * vectorLaplacian d2_u u i + grad_p i

/-- Cylindrical radial momentum residual ℛ_r(u, p) at ν = 1 (Equation 20, page 9). -/
noncomputable def cylindricalResidual_r (ur uθ uz : ℝ)
    (dt_ur dr_ur d2r_ur dz_ur d2z_ur dr_p : ℝ) (r : ℝ) : ℝ :=
  dt_ur + (ur * dr_ur + uz * dz_ur) - (uθ^2 / r) + dr_p
    - (d2r_ur + dr_ur / r - ur / (r^2) + d2z_ur)

/-- Cylindrical azimuthal momentum residual ℛ_θ(u, p) at ν = 1 (Equation 21, page 9). -/
noncomputable def cylindricalResidual_θ (ur uθ uz : ℝ)
    (dt_uθ dr_uθ d2r_uθ dz_uθ d2z_uθ : ℝ) (r : ℝ) : ℝ :=
  dt_uθ + (ur * dr_uθ + uz * dz_uθ) + (ur * uθ / r)
    - (d2r_uθ + dr_uθ / r - uθ / (r^2) + d2z_uθ)

/-- Cylindrical axial momentum residual ℛ_z(u, p) at ν = 1 (Equation 22, page 9). -/
noncomputable def cylindricalResidual_z (ur uz : ℝ)
    (dt_uz dr_uz d2r_uz dz_uz d2z_uz dz_p : ℝ) (r : ℝ) : ℝ :=
  dt_uz + (ur * dr_uz + uz * dz_uz) + dz_p
    - (d2r_uz + dr_uz / r + d2z_uz)

/-- Non-vacuous representation of `CandidateProperties` from `ProblemStatement.lean` (page 14):
    Explicitly encodes the residual operator `res`, divergence operator `div_u`, kinetic energy `E`,
    and supremum norm `sup_u` on [0, 1). -/
structure CandidateProperties (res : VelocityField) (div_u : ℝ × Space → ℝ)
    (E : ℝ → ℝ) (sup_u : ℝ → ℝ) where
  u : VelocityField
  p : PressureField
  f : VelocityField
  initial_rest : ∀ x : Space, u (0, x) = zeroVec
  extended_rest : ∀ (t : ℝ) (x : Space), |t| ≤ (3:ℝ)/8 →
    u (t, x) = zeroVec ∧ p (t, x) = 0 ∧ f (t, x) = zeroVec
  div_free : ∀ (t : ℝ) (x : Space), 0 ≤ t → t < 1 → div_u (t, x) = 0
  navier_stokes : ∀ (t : ℝ) (x : Space), 0 ≤ t → t < 1 → res (t, x) = f (t, x)
  kinetic_energy_bounded : ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → t < 1 → E t ≤ M
  speed_unbounded : ∀ M : ℝ, ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ M < sup_u t

/-- Verbatim representation of `cutStage` from `SolenoidalDiagonal.lean` (page 31). -/
noncomputable def cutStage (χ : ℝ → ℝ) (a_j : ℝ) (q : ℝ) (Δu_j : Space) : Space :=
  fun i => χ (a_j * q) * Δu_j i

/-- Verbatim representation of `potentialSum` from `SolenoidalDiagonal.lean` (page 31). -/
noncomputable def potentialSum (χ : ℝ → ℝ) (a : ℕ → ℝ) (q : ℝ) (Δu : ℕ → Space) (J : ℕ) : Space :=
  fun i => (List.range (J + 1)).foldl (fun acc j => acc + cutStage χ (a j) q (Δu j) i) 0

/-- Non-vacuous representation of `GlobalSmoothSolution` from `ComparatorR3Theorem.lean` (page 41). -/
structure GlobalSmoothSolution (ν : ℝ) (f : VelocityField) where
  u : VelocityField
  p : PressureField
  res : VelocityField
  div_u : ℝ × Space → ℝ
  E : ℝ → ℝ
  nu_pos : 0 < ν
  initial_rest : ∀ x : Space, u (0, x) = zeroVec
  div_free : ∀ (t : ℝ) (x : Space), 0 ≤ t → div_u (t, x) = 0
  momentum_eq : ∀ (t : ℝ) (x : Space), 0 ≤ t → res (t, x) = f (t, x)
  energy_finite : ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → E t ≤ M

/-- Alias for `GlobalFiniteEnergySolution` from `R3/Theorem.lean` (page 14). -/
abbrev GlobalFiniteEnergySolution (ν : ℝ) (f : VelocityField) : Type :=
  GlobalSmoothSolution ν f

/-- Spatial Schwartz decay condition (Equation 2, page 4):
    For every multi-index α and polynomial weight K, sup_x (1 + |x|)^K |∂^α u₀(x)| < ∞. -/
def IsSchwartzDecay (deriv_norm : (Fin 3 → ℕ) → Space → ℝ) (norm_x : Space → ℝ) : Prop :=
  ∀ (α : Fin 3 → ℕ) (K : ℕ), ∃ C_αK : ℝ, ∀ x : Space,
    (1 + norm_x x) ^ K * deriv_norm α x ≤ C_αK

/-- Formal existential statement of Theorem 1.1 (Equations 1–3, page 4). -/
def Theorem1_1_Statement (ν : ℝ) (res : VelocityField) (div_u : ℝ × Space → ℝ)
    (E : ℝ → ℝ) (sup_u : ℝ → ℝ) : Prop :=
  ∃ (cand : CandidateProperties res div_u E sup_u),
    ¬ Nonempty (GlobalSmoothSolution ν cand.f)
