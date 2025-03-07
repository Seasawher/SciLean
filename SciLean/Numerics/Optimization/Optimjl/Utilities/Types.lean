import SciLean.Data.DataArray
import SciLean.Tactic.DataSynth.HasRevFDerivUpdate
import SciLean.Meta.Notation.Do

/-! Port of Optim.jl, file src/types.jl

github link:
https://github.com/JuliaNLSolvers/Optim.jl/blob/711dfec61acf5dbed677e1af15f2a3347d5a88ad/src/types.jl

-/

namespace SciLean.Optimjl

structure Options (R : Type) [RealScalar R] where
  x_abstol : R := 0
  x_reltol : R := 0
  f_abstol : R := 0
  f_reltol : R := 0
  g_abstol : R := 1e-8
  g_reltol : R := 1e-8
  outer_x_abstol : R := 0
  outer_x_reltol : R := 0
  outer_f_abstol : R := 0
  outer_f_reltol : R := 0
  outer_g_abstol : R := 1e-8
  outer_g_reltol : R := 1e-8
  f_calls_limit : ℕ := 0
  g_calls_limit : ℕ := 0
  h_calls_limit : ℕ := 0
  allow_f_increases : Bool := true
  allow_outer_f_increases : Bool := true
  successive_f_tol : ℕ := 1
  iterations : ℕ := 1000
  outer_iterations : ℕ := 1000
  store_trace : Bool := false
  trace_simplex : Bool := false
  show_trace : Bool := false
  extended_trace : Bool := false
  show_warnings : Bool := true
  show_every: ℕ := 1
  callback : Unit → IO Unit := fun _ => pure ()
  time_limit? : Option ℕ := none


structure Method where
  isNewton : Bool
  isNewtonTrustRegion : Bool
  isNelderMead : Bool


structure MultivariateOptimizationResults (R X : Type) where
    initial_x : X
    minimizer : X
    minimum : R
    iterations : ℕ
    iteration_converged : Bool
    x_converged : Bool
    x_abstol : R
    x_reltol : R
    x_abschange : R -- Tc
    x_relchange : R -- Tc
    f_converged : Bool
    f_abstol : R
    f_reltol : R
    f_abschange : R -- Tc
    f_relchange : R -- Tc
    g_converged : Bool
    g_abstol : R
    g_residual : R -- Tc
    f_increased : Bool
    -- trace::M
    f_calls : ℕ
    g_calls : ℕ
    h_calls : ℕ
    ls_success : Bool
    time_limit? : Option ℕ
    time_run : ℕ
    -- stopped_by::Tsb

namespace MultivariateOptimizationResults

variable {R} {X} [RealScalar R] [ToString R] [ToString X]
variable (r : MultivariateOptimizationResults R X)

def converged : Bool :=
    let conv_flags := r.x_converged || r.f_converged || r.g_converged
    let x_isfinite := true -- isfinite(x_abschange(r)) || isnan(x_relchange(r))
    let f_isfinite := true
        -- if r.iterations > 0 then
        --     isfinite(f_abschange(r)) || isnan(f_relchange(r))
        -- else
        --     true
        -- end
    let g_isfinite := true -- isfinite(g_residual(r))
    conv_flags && x_isfinite && f_isfinite && g_isfinite

open IO in
def print : IO Unit := do
    -- take = Iterators.take

    let mut status_string := ""
    if r.converged then
      status_string := "success"
    else
      status_string := "failure"

    if r.iteration_converged then
      status_string := status_string ++ " (reached maximum number of iterations)"

    if r.f_increased && !r.iteration_converged then
      status_string := status_string ++ " (objective increased between iterations)"

    if !r.ls_success then
      status_string := status_string ++ " (line search failed)"

    if let some tl := r.time_limit? then
      if r.time_run > tl then
        status_string := status_string ++ " (exceeded time limit of $(time_limit(r)))"


    IO.print s!" * Status: {status_string}\n\n"

    IO.print " * Candidate solution\n"
    IO.print s!"    Final objective value:     {r.minimum}\n"
    IO.print s!"\n"

    IO.print s!" * Found with\n"
    IO.print s!"    Algorithm:     (TODO: implement this)\n"


    IO.print s!"\n"
    IO.print s!" * Convergence measures\n"
    -- if r.method.isNelderMead then
    --     IO.print s!"    √(Σ(yᵢ-ȳ)²)/n {(if r.g_converged then "≤" else "≰")} {r.g_abstol}\n"
    -- else
    if true then
      IO.print s!"    |x - x'|               = {r.x_abschange} {if r.x_abschange<=r.x_abstol then "≤" else "≰"} {r.x_abstol}\n"
      IO.print s!"    |x - x'|               = {r.x_relchange} {if r.x_relchange<=r.x_reltol then "≤" else "≰"} {r.x_reltol}\n"
      IO.print s!"    |f(x) - f(x')|         = {r.f_abschange} {if r.f_abschange<=r.f_abstol then "≤" else "≰"} {r.f_abstol}\n"
      IO.print s!"    |f(x) - f(x')|/|f(x')| = {r.f_relchange} {if r.f_relchange<=r.f_reltol then "≤" else "≰"} {r.f_reltol}\n"
      IO.print s!"    |g(x)|                 = {r.g_residual} {if r.g_residual<=r.g_abstol then "≤" else "≰"} {r.g_abstol}\n"

    IO.print s!"\n"

    IO.print s!" * Work counters\n"
    IO.print s!"    Seconds run:   {r.time_run}ns   (vs limit {if let some tl := r.time_limit? then toString tl else "∞"}ns)\n"
    IO.print s!"    Iterations:    {r.iterations}\n"
    IO.print s!"    f(x) calls:    {r.f_calls}\n"
    -- if !(isa(r.method, NelderMead) || isa(r.method, SimulatedAnnealing))
    IO.print s!"    ∇f(x) calls:   {r.g_calls}\n"
    -- if isa(r.method, Newton) || isa(r.method, NewtonTrustRegion)
    IO.print s!"    ∇²f(x) calls:  {r.h_calls}\n"

end MultivariateOptimizationResults


structure OptimizationState (R : Type) [RealScalar R] where
    iteration : ℕ
    value : R
    g_norm : R
    --metadata : Dict


structure ObjectiveFunction (R X : Type) [RealScalar R] [NormedAddCommGroup X] [AdjointSpace R X] where
  f : X → R
  f' : X → R × (R → X)
  hf : HasRevFDeriv R f f'

variable
  {R : Type} [RealScalar R]
  {X : Type} [NormedAddCommGroup X] [AdjointSpace R X] [CompleteSpace X]


variable (R X)
class AbstractOptimizerState (S : Type) (Method : Type) where
  initialConvergence (d : ObjectiveFunction R X) (state : S) (x₀ : X) (options : Options R) : (Bool×Bool)
  assessConvergence (state : S) (d : ObjectiveFunction R X) (options : Options R) : (Bool×Bool×Bool×Bool)

  updateState (d : ObjectiveFunction R X) (state : S) (method : Method) : (S×Bool)
  updateFG (d : ObjectiveFunction R X) (state : S) (method : Method) : S
  updateH (d : ObjectiveFunction R X) (state : S) (method : Method) : S

  pick_best_x (f_inc_pick : Bool) (state : S) : X
  pick_best_f (f_inc_pick : Bool) (state : S) (d : ObjectiveFunction R X) : R

  x_abschange (state : S) : R
  x_relchange (state : S) : R
  f_abschange (d : ObjectiveFunction R X) (state : S) : R
  f_relchange (d : ObjectiveFunction R X) (state : S) : R
  g_residual (d : ObjectiveFunction R X) (state : S) : R

  f_calls (d : ObjectiveFunction R X) (state : S) : ℕ
  g_calls (d : ObjectiveFunction R X) (state : S) : ℕ
  h_calls (d : ObjectiveFunction R X) (state : S) : ℕ

export AbstractOptimizerState (initialConvergence assessConvergence updateState updateFG updateH
       pick_best_x pick_best_f x_abschange x_relchange f_abschange f_relchange g_residual
       f_calls g_calls h_calls)
